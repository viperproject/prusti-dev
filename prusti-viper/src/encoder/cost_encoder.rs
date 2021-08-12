use prusti_common::vir;
use std::collections::{HashMap, HashSet, BTreeMap, BTreeSet};
use crate::encoder::places::Local;
use ::log::{trace, debug};
use crate::encoder::errors::{SpannedEncodingError, ErrorCtxt, WithSpan, EncodingError, SpannedEncodingResult};
use crate::encoder::mir_interpreter::{BackwardMirInterpreter, PureBackwardSubstitutionState, run_backward_interpretation};
use prusti_interface::specs::typed;
use crate::encoder::procedure_encoder::ProcedureEncoder;
use crate::encoder::Encoder;
use crate::encoder::mir_encoder::{MirEncoder, PlaceEncoder, PlaceEncoding};
use std::cmp::{Ordering, max};
use rustc_middle::mir;
use rustc_middle::mir::TerminatorKind;
use rustc_middle::ty;
use crate::encoder::pure_function_encoder::{PureFunctionEncoder, PureFunctionBackwardInterpreter};
use crate::encoder::builtin_encoder::BuiltinFunctionKind;
use prusti_common::vir::Expr;
use prusti_interface::data::ProcedureDefId;
use prusti_common::vir::ExprIterator;
use prusti_common::vir_local;
use itertools::Itertools;
use std::fmt;


/// return expr to be inhaled, stmts to check asymptotic bounds & remaining (non-credit) assertions
pub fn encode_credit_preconditions<'a, 'p: 'a, 'v: 'p, 'tcx: 'v>(
    preconditions: &'a[typed::Assertion<'tcx>],
    encoded_args: &Vec<vir::Expr>,
    encoder: &Encoder<'v, 'tcx>,
    procedure_encoder: &ProcedureEncoder<'p, 'v, 'tcx>,
    mir_encoder: &MirEncoder<'p, 'v, 'tcx>,
    mir: &mir::Body<'tcx>,
    proc_def_id: ProcedureDefId,
    conditional: bool,
) -> SpannedEncodingResult<(Option<Expr>, Vec<vir::Stmt>, Vec<&'a typed::Assertion<'tcx>>)>
{
    let mut extracted_credits = vec![];
    let mut remaining_pres = vec![];
    for assertion in preconditions {
        if let Some(cond_credits) = extract_conditional_credits(assertion, encoded_args, encoder, mir, proc_def_id)? {
            let cond_credits_no_coeff = (
                cond_credits.0,
                cond_credits.1,
                cond_credits.2.into_iter()
                    .map(|(powers, _)| powers)
                    .collect::<BTreeSet<VirCreditPowers>>()
            );
            extracted_credits.push(cond_credits_no_coeff);
        }
        else {
            remaining_pres.push(assertion);
        }
    }

    if !extracted_credits.is_empty() {
        // infer concrete credits
        let cost_interpreter = CostBackwardInterpreter {
            encoder,
            procedure_encoder,
            pure_fn_interpreter: PureFunctionBackwardInterpreter::new(
                encoder,
                mir,
                proc_def_id,
                false,
                proc_def_id,                 //TODO: correct?
            ),
            mir_encoder,
            mir,
            proc_def_id,
            conditional,
        };
        if let Some(result_state) = run_backward_interpretation(mir, &cost_interpreter)? {
            let mut max_exponents = HashMap::new();
            let mut cond_acc_predicates = vec![];
            for (opt_cond, credit_type_cost) in result_state.cost {
                // overapprox e.g. (1, 2) & (2, 1) as (2, 2)        //TODO: make more precise?
                // store max. exponent per number of exponents
                let mut acc_predicates = vec![];
                for (credit_type, coeff_map) in credit_type_cost {
                    let curr_max_exponents: &mut HashMap<usize, u32> = max_exponents.entry(credit_type.clone()).or_default();
                    // cf. spec_encoder
                    for (vir_powers, coeff_expr) in coeff_map {
                        let mut pred_args = vec![];
                        let mut exponents = vec![];
                        let mut max_exponent = 0u32;
                        for (vir_base_expr, exp) in vir_powers.powers {
                            max_exponent = max(max_exponent, exp);
                            pred_args.push(vir_base_expr.base);
                            exponents.push(exp);
                        }

                        for i in 1..=exponents.len() {
                            curr_max_exponents.entry(i)
                                .and_modify(|curr_max| *curr_max = max(*curr_max, max_exponent))
                                .or_insert(max_exponent);
                        }

                        let pred_name = encoder.encode_credit_predicate_use(&credit_type, exponents);
                        let frac_perm = vir::FracPermAmount::new(box coeff_expr, box 1.into());          //TODO: fractions?

                        acc_predicates.push(vir::Expr::credit_access_predicate(
                            pred_name,
                            pred_args,
                            frac_perm,
                        ));
                    }
                }

                let conjoined_accs = acc_predicates.into_iter().conjoin();
                if let Some(cond) = opt_cond {
                    cond_acc_predicates.push(
                        vir::Expr::implies(cond, conjoined_accs)
                    );
                }
                else {
                    cond_acc_predicates.push(conjoined_accs);
                }
            }
            let concrete_cost_precond = cond_acc_predicates.into_iter().conjoin();

            // construct asymptotic cost check
            let bounds_map = compute_bound_combinations(&extracted_credits, conditional);
            let mut asymp_check_stmts = vec![];
            for (credit_type, cond_map) in bounds_map {
                // only check asymptotic bound if there are credits inhaled of that type
                if let Some(max_exps) = max_exponents.get(&credit_type) {
                    asymp_check_stmts.push(
                        vir::Stmt::comment(format!("Checking asymptotic bounds for {}:", credit_type))
                    );

                    let mut curr_stmts = vec![];
                    // iterate from highest to lowest asymptotic bound (in terms of dominance), since conditions may overlap
                    for (abstract_bound, opt_condition) in cond_map.into_iter().rev() {
                        // transform abstract bound representation
                        // into map from exponent tuples (vec) to base expressions
                        let mut allowed_powers_map: HashMap<Vec<u32>, Vec<Vec<Expr>>> = HashMap::new();
                        for vir_powers in abstract_bound {
                            let mut base_exprs = vec![];
                            let mut exponents = vec![];
                            for (vir_base, exp) in vir_powers.powers {
                                base_exprs.push(vir_base.base);
                                exponents.push(exp);
                            }
                            allowed_powers_map.entry(exponents)
                                .or_default()
                                .push(base_exprs);
                        }

                        // assert that all coefficients that would change the asymptotic bound are zero
                        // == permission amount is zero
                        let mut bound_check_stmts = vec![];
                        for (n_exps, max_exp) in max_exps {         //TODO: prettier order?
                            let mut quantifier_vars = vec![];
                            for i in 0..*n_exps {
                                let var_name = format!("credit_arg_{}", i);     //TODO: naming ok?
                                quantifier_vars.push(
                                    vir::LocalVar::new(var_name, vir::Type::Int)
                                );
                            }
                            let quantifier_var_exprs: Vec<vir::Expr> = quantifier_vars.iter().map(|var| vir::Expr::local(var.clone())).collect();
                            for exponents in (1u32..=*max_exp).combinations_with_replacement(*n_exps) {
                                let pred_name = encoder.encode_credit_predicate_use(&credit_type, exponents.clone());
                                let pred_instance = vir::Expr::predicate_instance(pred_name, quantifier_var_exprs.clone());
                                let perm_zero_expr = vir::Expr::perm_equality(
                                    pred_instance.clone(),
                                    vir::FracPermAmount::new(box 0.into(), box 1.into())
                                );

                                let quantifier_body = if let Some(base_vecs) = allowed_powers_map.remove(&exponents) {
                                    let mut lhs_vec = vec![];
                                    for base_exprs in base_vecs {
                                        let mut equality_vec = vec![];
                                        for i in 0..*n_exps {
                                            equality_vec.push(
                                                vir::Expr::eq_cmp(quantifier_var_exprs[i].clone(), base_exprs[i].clone())        //TODO: could avoid clone
                                            )
                                        }
                                        lhs_vec.push(
                                            vir::Expr::not(
                                                equality_vec.into_iter().conjoin()
                                            )
                                        )
                                    }

                                    vir::Expr::implies(
                                        lhs_vec.into_iter().conjoin(),
                                        perm_zero_expr,
                                    )
                                }
                                else {
                                    perm_zero_expr
                                };

                                bound_check_stmts.push(
                                    vir::Stmt::Assert(
                                        vir::Expr::forall(
                                            quantifier_vars.clone(),
                                            vec![vir::Trigger::new(vec![pred_instance])],
                                            quantifier_body
                                        ),
                                        vir::Position::default()            //TODO
                                    ));
                            }
                        }

                        if let Some(cond) = opt_condition {
                            curr_stmts = vec![
                                vir::Stmt::If(
                                    cond,
                                    bound_check_stmts,
                                    curr_stmts
                                )
                            ];
                        }
                        else {
                            bound_check_stmts.extend(curr_stmts);
                            curr_stmts = bound_check_stmts;
                        }
                    }

                    asymp_check_stmts.extend(curr_stmts);
                }
            }

            Ok((Some(concrete_cost_precond), asymp_check_stmts, remaining_pres))
        }
        else {
            unimplemented!("loops are not supported yet");
        }
    }
    else {
        Ok((None, vec![], remaining_pres))
    }
}

// used to define custom order relation
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct VirBaseExpr {
    base: vir::Expr,
}

impl fmt::Display for VirBaseExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.base)
    }
}

impl Ord for VirBaseExpr {
    fn cmp(&self, other: &Self) -> Ordering {
        self.base.to_string().cmp(&other.base.to_string())
    }
}

impl PartialOrd for VirBaseExpr {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl VirBaseExpr {
    fn uses_place(&self, target: &Expr) -> bool {
        self.base.find(target)
    }

    fn replace_place(self, target: &Expr, replacement: &Expr) -> Self {
        Self {
            base: self.base.replace_place(target, replacement)
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct VirCreditPowers {
    /// Product/vector of variables raised to nonnegative powers
    /// ordered by the base expressions
    powers: BTreeMap<VirBaseExpr, u32>,
}

impl fmt::Display for VirCreditPowers {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.powers.is_empty() {
            write!(f, "1")?;
        }
        else {
            write!(f, "{}", self.powers.iter().map(|(base, exp)| format!("{}^{}", base, exp)).join(" * "))?;
        }
        Ok(())
    }
}

impl VirCreditPowers {
    fn uses_place(&self, target: &Expr) -> bool {
        self.powers.keys().any(|base| base.uses_place(target))
    }

    fn replace_place(self, target: &Expr, replacement: &Expr) -> Self {
        let mut new_powers = BTreeMap::new();       //TODO: too expensive?
        for (base, exponent) in self.powers {
            new_powers.insert(
                base.replace_place(target, replacement),
                exponent
            );
        }
        Self {powers: new_powers}
    }
}

/*impl From<Vec<typed::CreditVarPower>> for VirCreditPowers {
    fn from(credit_var_powers: Vec<CreditVarPower>) -> Self {
        let mut powers = vec![];
        for pow in credit_var_powers {

        }
    }
}*/

impl PartialOrd for VirCreditPowers {
    /// compares by asymptotic dominance
    /// Some(Less) == dominates other
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let mut possibly_greater = true;
        let mut possibly_less = true;
        let mut self_iter = self.powers.iter();
        let mut other_iter = other.powers.iter();
        let mut curr_self = self_iter.next();
        let mut curr_other = other_iter.next();
        loop {
            if let Some((self_base, self_exp)) = curr_self {
                if let Some((other_base, other_exp)) = curr_other {
                    if self_base < other_base {
                        // since the bases are ordered,
                        // this means self contains a variable that isn't part of other
                        if !possibly_less {
                            // no order possible
                            return None;
                        }
                        possibly_greater = false;
                        curr_self = self_iter.next();
                    }
                    else if other_base < self_base {
                        // other contains a variable that isn't part of self
                        if !possibly_greater {
                            // no order possible
                            return None;
                        }
                        possibly_less = false;
                        curr_other = other_iter.next();
                    }
                    else {
                        // same base ==> compare exponent
                        if self_exp > other_exp {
                            if !possibly_less {
                                // no order possible
                                return None;
                            }
                            possibly_greater = false;
                        }
                        else if self_exp < other_exp {
                            if !possibly_greater {
                                // no order possible
                                return None;
                            }
                            possibly_less = false;
                        }

                        // advance both iterators
                        curr_self = self_iter.next();
                        curr_other = other_iter.next();
                    }
                }
                else {
                    // self contains a variable that isn't part of other
                    if !possibly_less {
                        // no order possible
                        return None;
                    }
                    else {
                        return Some(Ordering::Less);
                    }
                }
            }
            else { // self iterator has reached the end
                if curr_other.is_none() {
                    // both iterators reached the end
                    if possibly_less && possibly_greater {
                        return Some(Ordering::Equal);
                    }
                    else if possibly_less {
                        return Some(Ordering::Less);
                    }
                    else {      // possibly_greater needs to be true, since always check other when setting
                        return Some(Ordering::Greater);
                    }
                }
                else {
                    // other contains a variable that isn't part of self
                    if !possibly_greater {
                        // no order possible
                        return None;
                    }
                    else {
                        return Some(Ordering::Greater);
                    }
                }
            }

        }
    }
}

impl Ord for VirCreditPowers {
    /// extend dominance relation to a total order
    /// == lexicographical order, but comparison on exponent is inverted
    fn cmp(&self, other: &Self) -> Ordering {
        // could probably be written in a simpler way, but this way it is easier to make sure
        // that it agrees with PartialOrd
        let mut self_iter = self.powers.iter();
        let mut other_iter = other.powers.iter();
        let mut curr_self = self_iter.next();
        let mut curr_other = other_iter.next();
        loop {
            if let Some((self_base, self_exp)) = curr_self {
                if let Some((other_base, other_exp)) = curr_other {
                    if self_base < other_base {
                        // since the bases are ordered,
                        // this means self contains a variable that isn't part of other
                        return Ordering::Less;            // dominance == less or non-comparable
                    }
                    else if other_base < self_base {
                        // other contains a variable that isn't part of self
                        return Ordering::Greater;            // dominance == greater or non-comparable
                    }
                    else {
                        // same base ==> compare exponent
                        if self_exp > other_exp {
                            return Ordering::Less;            // dominance == less or non-comparable
                        }
                        else if self_exp < other_exp {
                            return Ordering::Greater;            // dominance == greater or non-comparable
                        }

                        // if equal, advance both iterators
                        curr_self = self_iter.next();
                        curr_other = other_iter.next();
                    }
                }
                else {
                    // self contains a variable that isn't part of other (& they are equal until now)
                    return Ordering::Less;            // dominance == less or non-comparable
                }
            }
            else { // self iterator has reached the end
                if curr_other.is_none() {
                    // both iterators reached the end without any element being unequal
                    return Ordering::Equal;
                }
                else {
                    // other contains a variable that isn't part of self (& they are equal until now)
                    return Ordering::Greater;
                }
            }

        }
    }
}

/*// wrapper to implement Ord
#[derive(Clone, Debug, PartialEq, Eq)]
struct SumOfVirCreditPowers {
    summands: HashSet<VirCreditPowers>,
}

impl PartialOrd for SumOfVirCreditPowers {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {

    }
}

impl Ord for SumOfVirCreditPowers {
    fn cmp(&self, other: &Self) -> Ordering {

    }
}*/


fn extract_credits<'v, 'tcx: 'v>(
    abstract_terms: &Vec<typed::CreditPolynomialTerm>,
    encoded_args: &Vec<vir::Expr>,
    encoder: &Encoder<'v, 'tcx>,
    mir: &mir::Body<'tcx>,
    proc_def_id: ProcedureDefId,
) ->  SpannedEncodingResult<Vec<(VirCreditPowers, vir::Expr)>>
{
    let mut power_coeffs = vec![];
    for term in abstract_terms {
        let mut powers = BTreeMap::new();
        for pow in &term.powers {
            let base_assertion = typed::Assertion {               // "work-around" to be able to use encoder //TODO
                kind: Box::new(typed::AssertionKind::Expr(
                    typed::Expression {
                        spec_id: pow.spec_id,
                        id: pow.id,
                        expr: pow.base
                    }
                ))
            };

            let base_expr = encoder.encode_assertion(
                &base_assertion,
                mir,
                None,
                encoded_args,
                None,
                false,
                true,
                None,
                ErrorCtxt::GenericExpression,
                proc_def_id
            )?;

            powers.insert(
                VirBaseExpr { base: base_expr },
                pow.exponent
            );
        }
        let vir_credit_powers = VirCreditPowers { powers };

        let coeff_assertion = typed::Assertion {        // "work-around" to be able to use encoder //TODO
            kind: Box::new(typed::AssertionKind::Expr(term.coeff_expr.clone()))
        };
        let coeff_expr = encoder.encode_assertion(
            &coeff_assertion,
            mir,
            None,
            encoded_args,
            None,
            false,
            true,
            None,
            ErrorCtxt::GenericExpression,
            proc_def_id
        )?;
        power_coeffs.push((vir_credit_powers, coeff_expr));
    }

    Ok(power_coeffs)
}

/// returns credit_type, condition, coefficients
fn extract_conditional_credits<'v, 'tcx: 'v>(
    assertion: &typed::Assertion<'tcx>,
    encoded_args: &Vec<vir::Expr>,
    encoder: &Encoder<'v, 'tcx>,
    mir: &mir::Body<'tcx>,
    proc_def_id: ProcedureDefId
) -> SpannedEncodingResult<Option<(String, Option<vir::Expr>, Vec<(VirCreditPowers, vir::Expr)>)>>
{
    match &assertion.kind {
        box typed::AssertionKind::CreditPolynomial { credit_type, abstract_terms, .. } => {
            let power_coeffs = extract_credits(abstract_terms, encoded_args, encoder, mir, proc_def_id)?;
            Ok(Some((credit_type.clone(), None, power_coeffs)))
        }

        box typed::AssertionKind::Implies(condition,
                                          typed::Assertion {
                                              kind: box typed::AssertionKind::CreditPolynomial {
                                                  credit_type,
                                                  abstract_terms,
                                                  ..
                                              }
                                          })
        => {
            let vir_condition = encoder.encode_assertion(
                condition,
                mir,
                None,
                encoded_args,
                None,
                false,
                true,
                None,
                ErrorCtxt::GenericExpression,
                proc_def_id
            )?;
            let power_coeffs = extract_credits(abstract_terms, encoded_args, encoder, mir, proc_def_id)?;
            Ok(Some((credit_type.clone(), Some(vir_condition), power_coeffs)))
        }
        //TODO: other cases
        _ => Ok(None)
    }
}


/*fn compute_asymptotic_cost<'a>(all_powers: impl Iterator<Item=&'a VirCreditPowers>) -> BTreeSet<VirCreditPowers> {
    // invariant: All pairs in asymp_cost compare with dominates/partial_cmp == None
    let mut asymp_cost = BTreeSet::new();

    for new_powers in all_powers {
        let mut add_to_asymp_cost = true;
        let old_len = asymp_cost.len();
        let mut to_remove = vec![];
        for asymp_powers in &asymp_cost {       //TODO: optimize for ordered set
            match new_powers.partial_cmp(asymp_powers) {
                Some(Ordering::Less) => {
                    to_remove.push(asymp_powers.clone());   // new powers are dominate some asymp_powers
                }
                Some(Ordering::Greater) => {
                    add_to_asymp_cost = false;          // new powers are dominated by already added powers
                    break;      // there cannot be any already added powers that are dominated by new_powers, because domination is transitive
                }
                None => {}      // can still be dominated by another
                Some(Ordering::Equal) => unreachable!(),        //there shouldn't be two equal powers in all_powers
            }
        }

        for asymp_powers in to_remove {
            asymp_cost.remove(&asymp_powers);
        }

        debug_assert!(add_to_asymp_cost || old_len == asymp_cost.len());
        if add_to_asymp_cost {
            asymp_cost.insert(new_powers.clone());
        }
    }

    asymp_cost
}

fn asymptotic_least_upper_bound(left: &BTreeSet<VirCreditPowers>, right: &BTreeSet<VirCreditPowers>)
                                -> BTreeSet<VirCreditPowers>
{
    let mut result_set = BTreeSet::new();
    // add powers that are not dominated by any other
    'outer: for left_powers in left {       //TODO: optimize for ordered sets?
        for right_powers in right {
            match left_powers.partial_cmp(right_powers) {
                Some(Ordering::Less) => {
                    result_set.insert(left_powers.clone());
                    //TODO: could remove right_powers
                    continue 'outer;      // cannot be greater or equal any other
                }
                Some(Ordering::Greater) => {
                    result_set.insert(right_powers.clone());        // cannot be dominated by any left_powers due to transitivity
                    continue 'outer;
                }
                Some(Ordering::Equal) => {
                    // insert either one
                    result_set.insert(left_powers.clone());
                    continue 'outer;
                }
                None => {}
            }
        }
        // all comparisons have been 'None' => not dominated => insert
        result_set.insert(left_powers.clone());
    }
    result_set
}*/

fn compute_bound_combinations(abstract_credits: &[(String, Option<vir::Expr>, BTreeSet<VirCreditPowers>)], conditional: bool)
    -> BTreeMap<String, BTreeMap<BTreeSet<VirCreditPowers>, Option<vir::Expr>>>
{
    let mut result_map = BTreeMap::new();

    for (credit_type, opt_cond, abstract_cost) in abstract_credits {
        let credit_type_map: &mut BTreeMap<BTreeSet<VirCreditPowers>, Option<vir::Expr>>
            = result_map.entry(credit_type.clone()).or_default();

        let mut to_remove = vec![];
        let mut to_insert = vec![];       // or overwrite
        // combine new cost with all from before, if results in a new asymptotic cost
        // & add without combination, to generate all possible condition combinations
        for (curr_abstract_cost, curr_opt_cond) in credit_type_map.iter() {
            if conditional {
                match abstract_cost.partial_cmp(curr_abstract_cost) {     // check for asymptotic domination
                    Some(Ordering::Less) => {
                        if opt_cond.is_none() {
                            to_remove.push(curr_abstract_cost.clone());        // is dominated in any state
                        }
                    }
                    Some(Ordering::Greater) => {}
                    Some(Ordering::Equal) => {
                        // disjoin with current condition later
                    }
                    None => {
                        let mut upper_bound = curr_abstract_cost.clone();
                        upper_bound.extend(abstract_cost.clone());     // union
                        // conjoin conditions
                        if opt_cond.is_none() {
                            // overwrite abstract cost (will always be added to the current cost)
                            to_remove.push(curr_abstract_cost.clone());
                            to_insert.push((upper_bound, opt_cond.clone()));
                        } else {
                            // conjoin condition
                            let combined_cond = Some(curr_opt_cond.as_ref()
                                .map_or_else(|| opt_cond.clone().unwrap(),
                                     |curr_cond| vir::Expr::and(opt_cond.clone().unwrap(), curr_cond.clone())));
                            to_insert.push((upper_bound, combined_cond));
                        }
                    }
                }
            }
            else {      //TODO: don't add & remove, just compute conjunction once
                debug_assert!(credit_type_map.len() == 1);
                // no condition => all bounds get combined
                let mut upper_bound = curr_abstract_cost.clone();
                upper_bound.extend(abstract_cost.clone());     // union
                // replace abstract cost
                to_remove.push(curr_abstract_cost.clone());
                to_insert.push((upper_bound, None))
            }
        }

        // remove entries
        for key in to_remove {
            credit_type_map.remove(&key);
        }

        // add without conjunction
        credit_type_map.entry(abstract_cost.clone())
            .and_modify(|curr_opt_cond| *curr_opt_cond =
                curr_opt_cond.as_ref().zip_with(opt_cond.clone(), |curr_cond, cond| vir::Expr::or(cond, curr_cond.clone())))       // disjoin condition
            .or_insert(opt_cond.clone());

        // add entries
        for (insert_cost, insert_opt_cond) in to_insert {
            credit_type_map.entry(insert_cost)
                .and_modify(|curr_opt_cond| *curr_opt_cond =
                    curr_opt_cond.as_ref().zip_with(insert_opt_cond.clone(), |curr_cond, cond| vir::Expr::or(cond, curr_cond.clone())))       // disjoin condition
                .or_insert(insert_opt_cond);
        }
    }

    result_map
}


fn add_concrete_costs<'a>(
    coeff_map: &mut BTreeMap<VirCreditPowers, vir::Expr>,
    cost_to_add: impl Iterator<Item=(&'a VirCreditPowers, &'a vir::Expr)>)
{
    for (powers, coeff) in cost_to_add {
        if let Some(curr_coeff) = coeff_map.get_mut(powers) {
            *curr_coeff = vir::Expr::add(curr_coeff.clone(), coeff.clone());
        } else {
            coeff_map.insert(powers.clone(), coeff.clone());
        }
    }
}

type CostMap = Vec<(Option<vir::Expr>, BTreeMap<String, BTreeMap<VirCreditPowers, vir::Expr>>)>;        // use ordered sets/maps just for deterministic encoding

#[derive(Clone, Debug)]
struct CostBackwardInterpreterState {
    /// Map from credit type (string)       //TODO: update docu
    /// to map from asymptotic costs (Only contains powers that are not dominated by any other)
    /// to tuple of condition (lhs of implication)
    /// and map from powers to concrete coefficients
    ///
    /// This means we collect at most one implication per asymptotic cost,
    /// since more is not needed to prove (conditional) asymptotic bounds
    ///
    /// There might be different asymptotic costs with semantically overlapping conditions,
    /// but their check will be deferred to the verifier level
    cost: CostMap,
}

impl CostBackwardInterpreterState {
    fn substitute(&mut self, target: &Expr, replacement: Expr) {
        for (opt_condition, credit_cost) in &mut self.cost {
            *opt_condition = opt_condition.as_ref().map(|cond_expr| cond_expr.clone().replace_place(target, &replacement));      //TODO: avoid cloning?
            for coeff_map in credit_cost.values_mut() {
                // coefficients should only contain constants (& abstract coefficient function calls)
                // -> only replace in powers, but cannot directly modify the key!
                let use_target_in_power = coeff_map.keys().any(|powers| powers.uses_place(target));
                if use_target_in_power {
                    match replacement {
                        Expr::Local(..) => {
                            // simple 1:1-replacement
                            let mut new_map = BTreeMap::new();
                            //TODO: avoid cloning
                            let power_coeffs = coeff_map.into_iter()
                                .map(|(powers, coeff)|
                                    (powers.clone().replace_place(target, &replacement), coeff.clone()))        // coeff only contains only constants
                                .collect::<Vec<(VirCreditPowers, vir::Expr)>>();
                            add_concrete_costs(          // places may map to the same after replacement
                                &mut new_map,
                                power_coeffs.iter().map(|(a, b)| (a, b))        // convert &(A, B) into (&A, &B)
                            );
                            *coeff_map = new_map;
                        }
                        _ => {
                            unimplemented!("Assignment not supported");     //TODO: better error
                        }
                    }
                }
            }
        }
    }
}

impl PureBackwardSubstitutionState for CostBackwardInterpreterState {
    fn substitute_place(&mut self, sub_target: &Expr, replacement: Expr) {
        trace!("substitute_place {:?} --> {:?}", sub_target, replacement);

        //TODO: necessary?
        // If `replacement` is a reference, simplify also its dereferentiations
        if let vir::Expr::AddrOf(box ref base_replacement, ref _dereferenced_type, ref pos) =
        replacement
        {
            trace!("Substitution of a reference. Simplify its dereferentiations.");
            let deref_field = vir::Field::new("val_ref", base_replacement.get_type().clone());
            let deref_target = sub_target
                .clone()
                .field(deref_field.clone())
                .set_pos(*pos);
            self.substitute_place(&deref_target, base_replacement.clone());
        }

        self.substitute(sub_target, replacement);
    }

    fn substitute_value(&mut self, exact_target: &Expr, replacement: Expr) {
        self.substitute(exact_target, replacement);
    }

    fn use_place(&self, sub_target: &Expr) -> bool {
        self.cost.iter().any(|(opt_cond, credit_cost)|
            opt_cond.as_ref().map_or_else(|| false, |cond_expr| cond_expr.find(sub_target))
            ||
            credit_cost.values().any(|coeff_map|
                // don't check coefficients (should not contain any places)
                coeff_map.keys().any(|powers| powers.uses_place(sub_target))
            )
        )
    }
}

struct CostBackwardInterpreter<'a, 'p: 'a, 'v: 'p, 'tcx: 'v> {
    encoder: &'a Encoder<'v, 'tcx>,
    procedure_encoder: &'a ProcedureEncoder<'p, 'v, 'tcx>,
    pure_fn_interpreter: PureFunctionBackwardInterpreter<'p, 'v, 'tcx>,
    mir_encoder: &'a MirEncoder<'p, 'v, 'tcx>,
    mir: &'a mir::Body<'tcx>,
    proc_def_id: ProcedureDefId,
    conditional: bool,
}

impl<'a, 'p: 'a, 'v: 'p, 'tcx: 'v> CostBackwardInterpreter<'a, 'p, 'v, 'tcx> {
    fn insert_guarded_cost(
        &self,
        new_cost: &mut CostMap,
        target_cost: &CostMap,
        viper_guard: vir::Expr)
    {
        for (target_cond, target_credit_cost) in target_cost {
            if self.conditional {
                // conjoin the guard to the condition of the old concrete cost
                let new_target_condition =
                    if let Some(old_condition) = target_cond {
                        vir::Expr::and(viper_guard.clone(), old_condition.clone())
                    } else {
                        viper_guard.clone()
                    };

                new_cost.push((Some(new_target_condition), target_credit_cost.clone()));
            }
            else {
                debug_assert!(target_cond.is_none());

                if new_cost.is_empty() {
                    new_cost.push((None, target_credit_cost.clone()));
                }
                else {
                    debug_assert!(new_cost.len() == 1);
                    let (_, credit_cost) = new_cost.first_mut().unwrap();
                    // add coefficients
                    for (target_credit_type, target_coeff_map) in target_credit_cost {
                        let coeff_map = credit_cost.entry(target_credit_type.clone()).or_default();
                        add_concrete_costs(coeff_map, target_coeff_map.iter());
                    }
                }
            }
        }
    }

    fn add_cost(
        &self,
        curr_cost: &mut CostMap,
        credit_type: String,
        opt_condition: Option<vir::Expr>,
        power_coeffs: Vec<(VirCreditPowers, vir::Expr)>)
    {
        if self.conditional && opt_condition.is_some() {
            // add new conditioned cost
            // create map from power_coeffs
            let mut power_coeffs_map = BTreeMap::new();
            power_coeffs_map.extend(power_coeffs.clone());
            let mut credit_type_map = BTreeMap::new();
            credit_type_map.insert(credit_type, power_coeffs_map);
            curr_cost.push((opt_condition, credit_type_map));
        } else {      // addition of cost not dependent on a condition
            // add coefficients to all elements
            for (_, curr_credit_cost) in curr_cost {
                let coeff_map = curr_credit_cost.entry(credit_type.clone()).or_default();
                add_concrete_costs(coeff_map, power_coeffs.iter().map(|(a, b)| (a, b)));
            }
        }
    }
}

impl<'a, 'p: 'a, 'v: 'p, 'tcx: 'v> BackwardMirInterpreter<'tcx> for CostBackwardInterpreter<'a, 'p, 'v, 'tcx> {
    type Error = SpannedEncodingError;
    type State = CostBackwardInterpreterState;

    fn apply_terminator(&self, _bb: mir::BasicBlock, terminator: &mir::Terminator<'tcx>, states: HashMap<mir::BasicBlock, &Self::State>) -> Result<Self::State, Self::Error> {
        let term_span = terminator.source_info.span;
        //let location = self.mir.terminator_loc(bb);

        match terminator.kind {
            TerminatorKind::SwitchInt { switch_ty, ref discr, ref targets } => {//TODO: treat like asignment, but not single assignment! (only when constant?)
            trace!(
                    "SwitchInt ty '{:?}', discr '{:?}', targets '{:?}'",
                    switch_ty,
                    discr,
                    targets
                );

                let discr_val = self.mir_encoder.encode_operand_expr(discr).with_span(term_span)?;

                let mut new_cost: CostMap = vec![];
                let mut guard_disjunction = None;
                for (value, target) in targets.iter() {
                    // construct condition (cf. pure function encoder)
                    let viper_guard = match switch_ty.kind() {
                        ty::TyKind::Bool => {
                            if value == 0 {
                                // If discr is 0 (false)
                                vir::Expr::not(discr_val.clone().into())
                            } else {
                                // If discr is not 0 (true)
                                discr_val.clone().into()
                            }
                        }

                        ty::TyKind::Int(_) | ty::TyKind::Uint(_) => {
                            //TODO: eliminate discr_var from Powers since equal to constant
                            vir::Expr::eq_cmp(
                                discr_val.clone().into(),
                                self.encoder.encode_int_cast(value, switch_ty),
                            )
                        }

                        ref x => unreachable!("{:?}", x),
                    };

                    guard_disjunction = Some(guard_disjunction.map_or_else(|| viper_guard.clone(),
                                                                    |curr_guards| vir::Expr::or(viper_guard.clone(), curr_guards)));
                    self.insert_guarded_cost(&mut new_cost, &states[&target].cost, viper_guard);
                }

                let otherwise_guard = vir::Expr::not(guard_disjunction.unwrap());
                let otherwise_target = targets.otherwise();
                self.insert_guarded_cost(&mut new_cost, &states[&otherwise_target].cost, otherwise_guard);

                Ok(CostBackwardInterpreterState { cost: new_cost })
            }

            TerminatorKind::Call {
                ref args,
                ref destination,
                func:
                mir::Operand::Constant(box mir::Constant {
                    literal: mir::ConstantKind::Ty(
                        ty::Const {
                            ty,
                            val: _,
                        },
                    ),
                    ..
                }),
                ..
            } => {
                if let ty::TyKind::FnDef(def_id, substs) = ty.kind() {
                    let (target_local, target_block) = match destination.as_ref() {
                        Some((ref target_place, ref block)) => {
                            if let Some(target_local) = target_place.as_local() {
                                (target_local.into(), block)
                            } else {
                                unimplemented!()
                                /*//TODO: can support more, result cannot occur in credit (pre)condition
                                let (_, ty, _) = self.mir_encoder.encode_place(target_place)?;
                                self.procedure_encoder.locals.get_fresh(ty);*/        //TODO: modifies self
                            }
                        }
                        None => {
                            // The return type is Never
                            // This means that the function call never returns
                            // ==> cannot compute any concrete cost
                            unimplemented!("Non-terminating function call")
                            /*// Return a dummy local variable
                            let never_ty = self.encoder.env().tcx().mk_ty(ty::TyKind::Never);
                            self.locals.get_fresh(never_ty)*/
                        }
                    };

                    let mut new_state = states[target_block].clone();

                    //TODO: special cases (specific fn names)

                    if !self.encoder.is_pure(*def_id) {          // we do not support credit specifications for pure functions
                        if !self.encoder.env().tcx().is_closure(*def_id) {        // closures do not have pre- & postconditions
                            let self_ty = {
                                // If we are calling a trait method on a struct, self_ty
                                // is the struct.
                                let generics = self.encoder.env().tcx().generics_of(*def_id);
                                if generics.has_self {
                                    Some(substs.type_at(0))
                                } else {
                                    None
                                }
                            };

                            // Collect arguments ( = VIR Locals that will hold the argument before the call)
                            let mut argument_locals: Vec<Local> = vec![];

                            for arg in args.iter() {
                                argument_locals.push(
                                    arg.place()
                                        .and_then(|place| place.as_local())
                                        .map_or_else(
                                            || unimplemented!("Only locals as function call arguments are supported"),            // only local variables as arguments are supported      //TODO: check if contract contains credits first
                                            |local| local.into()
                                        )
                                );
                            }

                            let own_substs =
                                ty::List::identity_for_item(self.encoder.env().tcx(), *def_id);

                            // FIXME: this is a hack to support generics. See issue #187.
                            let mut tymap = HashMap::new();

                            for (kind1, kind2) in own_substs.iter().zip(substs.iter()) {
                                if let (
                                    ty::subst::GenericArgKind::Type(ty1),
                                    ty::subst::GenericArgKind::Type(ty2),
                                ) = (kind1.unpack(), kind2.unpack())
                                {
                                    tymap.insert(ty1, ty2);
                                }
                            }
                            // needed for procedure_contract        //TODO: correct?
                            let _cleanup_token = self.encoder.push_temp_tymap(tymap);

                            let procedure_contract = {
                                self.encoder.get_procedure_contract_for_call(
                                    self_ty,
                                    *def_id,
                                    &argument_locals,
                                    target_local,
                                ).with_span(term_span)?
                            };

                            let encoded_args: Vec<vir::Expr> = procedure_contract
                                .args
                                .iter()
                                .map(|local| self.procedure_encoder.encode_prusti_local(*local).into())
                                .collect();

                            // add new cost to current cost
                            let curr_cost = &mut new_state.cost;
                            let func_precondition = procedure_contract.functional_precondition();
                            for assertion in func_precondition {
                                if let Some((credit_type, opt_condition, power_coeffs)) =
                                extract_conditional_credits(assertion, &encoded_args, self.encoder, self.mir, self.proc_def_id)?      //TODO: here we assume only one credit expression per assertion
                                {
                                    self.add_cost(curr_cost, credit_type, opt_condition, power_coeffs);     //TODO: better (more efficient) to add all in one go?
                                }
                            }
                        }
                    }

                    Ok(new_state)
                } else {
                    unimplemented!();
                }
            }

            TerminatorKind::Call { .. } => {
                unimplemented!();
            }

            TerminatorKind::DropAndReplace {
                ref target,
                place: ref lhs,
                ref value,
                ..
            } => {
                let mut new_state = states[target].clone();
                new_state.apply_assignment(&self.pure_fn_interpreter, lhs, &mir::Rvalue::Use(value.clone()), term_span, self.proc_def_id)?;
                Ok(new_state)
            }

            TerminatorKind::Assert {
                ref cond,
                expected,
                ref target,
                ..
            } => {
                let cond_val = self.mir_encoder.encode_operand_expr(cond)
                    .with_span(term_span)?;
                let viper_guard = if expected {
                    cond_val
                } else {
                    vir::Expr::not(cond_val)
                };

                let mut new_cost = vec![];
                // ignore failure & add condition
                self.insert_guarded_cost(&mut new_cost, &states[target].cost, viper_guard);

                Ok(CostBackwardInterpreterState { cost: new_cost })
            }

            TerminatorKind::Goto { ref target } => {
                debug_assert_eq!(states.len(), 1);
                Ok(states[target].clone())
            }

            TerminatorKind::Drop { ref target, .. } => {
                debug_assert!(1 <= states.len() && states.len() <= 2);
                Ok(states[target].clone())
            }

            TerminatorKind::FalseEdge {
                ref real_target, ..
            } => {
                debug_assert_eq!(states.len(), 2);
                Ok(states[real_target].clone())
            }

            TerminatorKind::FalseUnwind {
                ref real_target, ..
            } => {
                debug_assert_eq!(states.len(), 1);
                Ok(states[real_target].clone())
            }

            TerminatorKind::Resume
            | TerminatorKind::Abort
            | TerminatorKind::Return
            | TerminatorKind::Unreachable => {
                // TOOD: error (for some)?
                // no cost
                Ok(CostBackwardInterpreterState { cost: vec![(None, BTreeMap::new())] })
            }

            _ => unimplemented!("{:?}", terminator.kind),
        }
    }

    fn apply_statement(&self, _bb: mir::BasicBlock, _stmt_index: usize, stmt: &mir::Statement<'tcx>, state: &mut Self::State) -> Result<(), Self::Error> {
        let stmt_span = stmt.source_info.span;
        /*let location = mir::Location {
            block: bb,
            statement_index: stmt_index,
        };*/

        match stmt.kind {
            mir::StatementKind::Assign(box (ref lhs, ref rhs)) => {
                state.apply_assignment(&self.pure_fn_interpreter, lhs, rhs, stmt_span, self.proc_def_id)?;
            }

            mir::StatementKind::FakeRead(..)
            | mir::StatementKind::StorageLive(..)
            | mir::StatementKind::StorageDead(..)
            | mir::StatementKind::AscribeUserType(..)
            | mir::StatementKind::Coverage(..)
            | mir::StatementKind::Nop => {}

            ref kind => unimplemented!("encoding of '{:?}'", kind)
        }

        Ok(())
    }
}