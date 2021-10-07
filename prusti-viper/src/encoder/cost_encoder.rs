use prusti_common::{vir, config};
use std::collections::{HashMap, HashSet, BTreeMap, BTreeSet};
use crate::encoder::places::{Local, LocalVariableManager};
use ::log::{trace, debug};
use crate::encoder::errors::{SpannedEncodingError, ErrorCtxt, WithSpan, EncodingError, SpannedEncodingResult, EncodingResult};
use crate::encoder::mir_interpreter::{BackwardMirInterpreter, PureBackwardSubstitutionState, run_backward_interpretation};
use prusti_interface::specs::typed;
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
use num_integer;

#[derive(Clone, Debug)]
pub(crate) struct CostEncoder<'tcx> {
    precondition: Option<vir::Expr>,
    recurrence_check: Vec<vir::Stmt>,
    asymp_bound_check: Vec<vir::Stmt>,
    pub(crate) remaining_func_pres: Vec<typed::Assertion<'tcx>>,
    conversions: HashMap<mir::Location, Vec<(Option<vir::Expr>, Vec<CreditConversion>)>>,   //TODO: generate Stmts here & add methods to encoder from here
}

impl<'a, 'p: 'a, 'v: 'p, 'tcx: 'v> CostEncoder<'tcx> {
    /// Cost encoder with empty result state
    pub(crate) fn new() -> Self {
        Self {
            precondition: None,
            recurrence_check: vec![],
            asymp_bound_check: vec![],
            remaining_func_pres: vec![],
            conversions: HashMap::new(),
        }
    }

    pub(crate) fn extract_precondition(&mut self) -> Option<vir::Expr> {
        self.precondition.take()
    }

    pub(crate) fn extract_recurrence_check_stmts(&mut self) -> Vec<vir::Stmt> {
        std::mem::take(&mut self.recurrence_check)
    }

    pub(crate) fn extract_asymp_bound_check_stmts(&mut self) -> Vec<vir::Stmt> {
        std::mem::take(&mut self.asymp_bound_check)
    }

    pub(crate) fn extract_conversions_for(&mut self, location: mir::Location) -> Vec<(Option<vir::Expr>, Vec<CreditConversion>)> {
        self.conversions.remove(&location).unwrap_or_else(|| vec![])
    }

    pub(crate) fn run_inference(
        &mut self,
        preconditions: Vec<typed::Assertion<'tcx>>,
        encoded_args: &Vec<vir::Expr>,
        encoder: &Encoder<'v, 'tcx>,
        mir_encoder: &MirEncoder<'p, 'v, 'tcx>,
        locals_manager: &LocalVariableManager<'tcx>,
        mir: &mir::Body<'tcx>,
        proc_def_id: ProcedureDefId,
        conditional: bool,
    ) -> SpannedEncodingResult<()>
    {
        let mut extracted_credits: Vec<(String, Option<Expr>, Vec<(VirCreditPowers, Expr)>)> = vec![];
        let mut abstract_coeff_var_replacements: HashMap<String, Vec<(vir::Expr, vir::Expr)>> = HashMap::new();
        let mut abstract_coeff_vars: HashMap<String, Vec<vir::LocalVar>> = HashMap::new();
        debug_assert!(self.remaining_func_pres.is_empty());
        let mut credit_assertion_spans = vec![];
        let mut conditional_annotation = false;
        for assertion in preconditions {
            if let Some((credit_type, opt_condition, power_coeffs)) = extract_conditional_credits(&assertion, encoded_args, encoder, mir, proc_def_id)? {
                let mut powers_coeff_var_exprs = vec![];
                for (powers, coeff) in power_coeffs {
                    let var_name = if let vir::Expr::FuncApp(name, ..) = &coeff {
                        format!("{}_v", name)
                    }
                    else {
                        unreachable!()
                    };
                    let local_var = vir::LocalVar::new(var_name, vir::Type::Int);
                    abstract_coeff_vars.entry(credit_type.clone())
                        .or_default()
                        .push(local_var.clone());
                    let var_expr = vir::Expr::local(local_var);
                    abstract_coeff_var_replacements.entry(credit_type.clone())
                        .or_default()
                        .push((coeff, var_expr.clone()));

                    powers_coeff_var_exprs.push((powers, var_expr));
                }

                conditional_annotation = conditional_annotation || opt_condition.is_some();

                extracted_credits.push((credit_type, opt_condition, powers_coeff_var_exprs));

                credit_assertion_spans.extend(
                    typed::Spanned::get_spans(&assertion, mir, encoder.env().tcx())
                )
            } else {
                self.remaining_func_pres.push(assertion);
            }
        }

        if !extracted_credits.is_empty() {
            // infer concrete credits
            let cost_interpreter = CostBackwardInterpreter {
                    encoder,
                    pure_fn_interpreter: PureFunctionBackwardInterpreter::new(
                        encoder,
                        mir,
                        proc_def_id,
                        false,
                        proc_def_id,                 //TODO: correct?
                    ),
                    mir_encoder,
                    locals_manager,
                    mir,
                    proc_def_id,
                    conditional: conditional && conditional_annotation,
                };

            trace!("Running credit inference backward interpretation");
            if let Some(result_state) = run_backward_interpretation(mir, &cost_interpreter)? {
                self.conversions = result_state.conversions;

                // Construct precondition & cost with recursive coeff replacement from inferred cost
                let mut type_to_exponents = HashMap::new();
                let mut cond_acc_predicates = vec![];
                let mut cost_with_replacements = result_state.cost;
                let mut is_recursive = false;
                for (opt_cond, credit_type_cost) in cost_with_replacements.iter_mut() {
                    // overapprox e.g. (1, 2) & (2, 1) as (2, 2)        //TODO: make more precise?
                    // store max. exponent per number of exponents
                    let mut acc_predicates = vec![];
                    for (credit_type, coeff_map) in credit_type_cost {
                        let coeff_replacements = abstract_coeff_var_replacements.get(credit_type);
                        let exponents_set: &mut BTreeSet<Vec<u32>> = type_to_exponents.entry(credit_type.clone()).or_default();
                        // cf. spec_encoder
                        for (vir_powers, coeff_expr) in coeff_map {
                            let mut pred_args = vec![];
                            let mut exponents = vec![];
                            for (vir_base_expr, exp) in &vir_powers.powers {
                                pred_args.push(vir_base_expr.base.clone());
                                exponents.push(*exp);
                            }
                            if !exponents.is_empty() {
                                exponents_set.insert(exponents.clone());
                            }

                            let pred_name = encoder.encode_credit_predicate_use(&credit_type, exponents, vir_powers.negative);
                            let frac_perm = vir::FracPermAmount::new(box coeff_expr.clone(), box 1.into());          //TODO: fractions?

                            acc_predicates.push(vir::Expr::credit_access_predicate(
                                pred_name,
                                pred_args,
                                frac_perm,
                            ));

                            if let Some(replacements) = coeff_replacements {
                                let recurrence_coeff_expr = coeff_expr.clone().replace_sub_expressions(replacements);
                                is_recursive = is_recursive || (recurrence_coeff_expr != *coeff_expr);
                                *coeff_expr = recurrence_coeff_expr;
                            }
                        }
                    }

                    let conjoined_accs = acc_predicates.into_iter().conjoin();
                    if let Some(cond) = opt_cond {
                        cond_acc_predicates.push(
                            vir::Expr::implies(cond.clone(), conjoined_accs)
                        );
                    } else {
                        cond_acc_predicates.push(conjoined_accs);
                    }
                }
                self.precondition = Some(cond_acc_predicates.into_iter().conjoin());

                if config::verify_finite_credits() && is_recursive {
                    // Construct conditional recurrence check
                    let mut type_cond_rec_checks: HashMap<String, Vec<vir::Expr>> = HashMap::new();
                    // conditions from annotation
                    for (credit_type, opt_cond, powers_coeff) in &extracted_credits {
                        let mut inferred_cond_rec_check = vec![];
                        // inferred conditions
                        for (inferred_opt_cond, credit_type_cost) in &cost_with_replacements {
                            if let Some(coeff_map) = credit_type_cost.get(credit_type) {
                                let mut coeff_comparisons = vec![];
                                for (powers, coeff_var) in powers_coeff {
                                    debug_assert!(!powers.negative);
                                    let opt_inferred_pos_coeff = coeff_map.get(powers);
                                    let mut neg_powers = powers.clone();
                                    neg_powers.negative = true;
                                    let inferred_coeff = if let Some(inferred_neg_coeff) = coeff_map.get(&neg_powers) {
                                        if let Some(inferred_pos_coeff) = opt_inferred_pos_coeff {
                                            vir::Expr::sub(inferred_pos_coeff.clone(), inferred_neg_coeff.clone())
                                        }
                                        else {
                                            vir::Expr::minus(inferred_neg_coeff.clone())
                                        }
                                    }
                                    else {
                                        if let Some(inferred_pos_coeff) = opt_inferred_pos_coeff {
                                            inferred_pos_coeff.clone()
                                        }
                                        else {
                                            continue; // no inferred coeff for these powers
                                        }
                                    };

                                    coeff_comparisons.push(
                                        vir::Expr::ge_cmp(
                                            coeff_var.clone(),
                                            inferred_coeff,
                                        )
                                    )
                                }
                                if !coeff_comparisons.is_empty() {
                                    let conjoined_coeff_comparisons = coeff_comparisons.into_iter().conjoin();
                                    if let Some(cond) = inferred_opt_cond {
                                        inferred_cond_rec_check.push(
                                            vir::Expr::implies(cond.clone(), conjoined_coeff_comparisons)
                                        );
                                    } else {
                                        inferred_cond_rec_check.push(conjoined_coeff_comparisons);
                                    }
                                }
                            }
                        }

                        if !inferred_cond_rec_check.is_empty() {
                            let conjoined_inferred_cond_rec_check = inferred_cond_rec_check.into_iter().conjoin();
                            if let Some(cond) = opt_cond {
                                type_cond_rec_checks.entry(credit_type.clone())
                                    .or_default()
                                    .push(
                                        vir::Expr::implies(cond.clone(), conjoined_inferred_cond_rec_check)
                                    );
                            } else {
                                type_cond_rec_checks.entry(credit_type.clone())
                                    .or_default()
                                    .push(conjoined_inferred_cond_rec_check);
                            }
                        }
                    }

                    debug_assert!(self.recurrence_check.is_empty());
                    for (credit_type, cond_rec_checks) in type_cond_rec_checks {
                        self.recurrence_check.push(
                            vir::Stmt::comment(format!("Checking termination of the recursion for {}:", credit_type))
                        );
                        let error_pos = encoder
                            .error_manager()
                            .register(credit_assertion_spans.clone(), ErrorCtxt::AssertTerminatingRecurrence, proc_def_id);
                        self.recurrence_check.push(vir::Stmt::Assert(
                            vir::Expr::exists(
                                abstract_coeff_vars.remove(&credit_type).unwrap(),
                                vec![],
                                cond_rec_checks.into_iter().conjoin(),
                            ),
                            error_pos,
                        ));
                    }
                }

                // remove coeffs from extracted_credits
                let extracted_credits_no_coeff: Vec<(String, Option<Expr>, BTreeSet<VirCreditPowers>)> =
                    extracted_credits.into_iter()
                        .map(|(credit_type, opt_cond, power_coeffs)|
                             (
                                 credit_type,
                                 opt_cond,
                                 power_coeffs.into_iter()
                                    .map(|(powers, _)| powers)
                                    .collect(),
                             )
                        )
                        .collect();

                // Construct asymptotic cost check
                let bounds_map = compute_bound_combinations(&extracted_credits_no_coeff, conditional && conditional_annotation);
                debug_assert!(self.asymp_bound_check.is_empty());
                for (credit_type, cond_map) in bounds_map {
                    // only check asymptotic bound if there are credits inhaled of that type & only check inhaled exponents
                    if let Some(exponents_set) = type_to_exponents.get(&credit_type) {
                        self.asymp_bound_check.push(
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
                            // TODO: more fine-grained spans pointing to 1 assertion
                            let error_pos = encoder
                                .error_manager()
                                .register(credit_assertion_spans.clone(), ErrorCtxt::AssertAsymptoticBound, proc_def_id);
                            let mut bound_check_stmts = vec![];
                            for exponents in exponents_set.iter().rev() {
                                let mut quantifier_vars = vec![];
                                for i in 0..exponents.len() {
                                    let var_name = format!("c_arg_{}", i);     //TODO: naming ok?
                                    quantifier_vars.push(
                                        vir::LocalVar::new(var_name, vir::Type::Int)
                                    );
                                }
                                let quantifier_var_exprs: Vec<vir::Expr> = quantifier_vars.iter().map(|var| vir::Expr::local(var.clone())).collect();

                                let pred_name = encoder.encode_credit_predicate_use(&credit_type, exponents.clone(), false);
                                let pred_instance = vir::Expr::predicate_instance(pred_name, quantifier_var_exprs.clone());
                                /*// TODO: should not be necessary?
                                let neg_pred_name = encoder.encode_credit_predicate_use(&credit_type, exponents.clone(), true);
                                let neg_pred_instance = vir::Expr::predicate_instance(neg_pred_name, quantifier_var_exprs.clone());*/
                                let perm_zero_expr = vir::Expr::perm_equality(
                                    pred_instance.clone(),
                                    vir::FracPermAmount::new(box 0.into(), box 1.into())
                                );

                                let quantifier_body = if let Some(base_vecs) = allowed_powers_map.remove(exponents) {
                                    let mut lhs_vec = vec![];
                                    for base_exprs in base_vecs {
                                        let mut equality_vec = vec![];
                                        for i in 0..exponents.len() {
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
                                } else {
                                    perm_zero_expr
                                };

                                bound_check_stmts.push(
                                    vir::Stmt::Assert(
                                        vir::Expr::forall(
                                            quantifier_vars.clone(),
                                            vec![vir::Trigger::new(vec![pred_instance])],
                                            quantifier_body
                                        ),
                                        error_pos
                                    ));
                            }

                            if let Some(cond) = opt_condition {
                                curr_stmts = vec![
                                    vir::Stmt::If(
                                        cond,
                                        bound_check_stmts,
                                        curr_stmts
                                    )
                                ];
                            } else {
                                bound_check_stmts.extend(curr_stmts);
                                curr_stmts = bound_check_stmts;
                            }
                        }

                        self.asymp_bound_check.extend(curr_stmts);
                    }
                }
            } else {
                unimplemented!("loops are not supported yet");
            }
        }
        Ok(())
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
    negative: bool,
    /// Product/vector of variables raised to nonnegative powers
    /// ordered by the base expressions
    powers: BTreeMap<VirBaseExpr, u32>,
}

impl fmt::Display for VirCreditPowers {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.negative {
            write!(f, "-")?;
        }
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
    fn base_exprs(&self) -> Vec<vir::Expr> {
        self.powers.iter()
            .map(|(base, _)| base.base.clone())
            .collect()
    }

    fn exponents(&self) -> Vec<u32> {
        self.powers.iter()
            .map(|(_, exp)| exp.clone())
            .collect()
    }

    fn get_index(&self, base_expr: &Expr) -> Option<usize> {
        self.powers.keys().position(|vir_base| vir_base.base == *base_expr)     //TODO: optimization?
    }

    fn uses_place(&self, target: &Expr) -> bool {
        self.powers.keys().any(|base| base.uses_place(target))
    }

    /// returns new base expressions with replacement//TODO: doc
    fn replace_place(&mut self, target: &Expr, replacement: &Expr) -> (Vec<usize>, Vec<(Expr, bool)>) {
        let mut base_replacements = vec![];
        let mut replaced_indices = vec![];
        for (idx, base) in self.powers.keys().enumerate() {
            let base_with_replacement = base.clone().replace_place(target, replacement);
            if &base_with_replacement != base {
                replaced_indices.push(idx);
                base_replacements.push((base.clone(), base_with_replacement));
            }
        }

        let mut res_vec = vec![];
        for (base, base_with_replacement) in base_replacements {
            if let Some(exp) = self.powers.remove(&base) {
                if let Some(curr_exp) = self.powers.get_mut(&base_with_replacement) {
                    res_vec.push((base_with_replacement.base.clone(), false));
                    *curr_exp += exp;
                } else {
                    res_vec.push((base_with_replacement.base.clone(), true));
                    self.powers.insert(base_with_replacement, exp);
                }
            }
            else {
                unreachable!()
            }
        }
        (replaced_indices, res_vec)
    }

    fn remove_power(&mut self, base: vir::Expr) -> Option<u32> {
        self.powers.remove(&VirBaseExpr { base })
    }

    fn insert_power(&mut self, base: vir::Expr, exponent: u32) -> bool {
        let vir_base = VirBaseExpr { base };
        if let Some(curr_exp) = self.powers.get_mut(&vir_base) {
            *curr_exp += exponent;
            false
        }
        else {
            self.powers.insert(vir_base, exponent);
            true
        }
    }

    fn get_exponent(&self, base: vir::Expr) -> Option<&u32> {
        self.powers.get(&VirBaseExpr { base })
    }

    fn set_exponent(&mut self, base: vir::Expr, exponent: u32) -> bool {
        let opt_exp = self.powers.get_mut(&VirBaseExpr { base });
        if let Some(exp_ref) = opt_exp {
            *exp_ref = exponent;
            true
        }
        else {
            false
        }
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
        if self.negative && !other.negative {
            // self dominated by other
            return Some(Ordering::Greater);
        }
        else if !self.negative && other.negative {
            // self dominates other
            return Some(Ordering::Less);
        }

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
                        if self.negative && other.negative {
                            // inverse order
                            return Some(Ordering::Greater);
                        }
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
                    else if (possibly_less && !self.negative && !other.negative)
                            || (possibly_greater && self.negative && other.negative) {        // inverse order
                        return Some(Ordering::Less);
                    }
                    else {      // possibly_greater needs to be true, since always check other when setting (or both are negative)
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
                        if self.negative && other.negative {
                            // inverse order
                            return Some(Ordering::Less);
                        }
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

        if self.negative && !other.negative {
            // self dominated by other
            return Ordering::Greater;
        }
        else if !self.negative && other.negative {
            // self dominates other
            return Ordering::Less;
        }

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
                        if self.negative && other.negative {
                            // inverse order
                            return Ordering::Greater;
                        }
                        return Ordering::Less;            // dominance == less or non-comparable
                    }
                    else if other_base < self_base {
                        // other contains a variable that isn't part of self
                        if self.negative && other.negative {
                            // inverse order
                            return Ordering::Less;
                        }
                        return Ordering::Greater;            // dominance == greater or non-comparable
                    }
                    else {
                        // same base ==> compare exponent
                        if self_exp > other_exp {
                            if self.negative && other.negative {
                                // inverse order
                                return Ordering::Greater;
                            }
                            return Ordering::Less;            // dominance == less or non-comparable
                        }
                        else if self_exp < other_exp {
                            if self.negative && other.negative {
                                // inverse order
                                return Ordering::Less;
                            }
                            return Ordering::Greater;            // dominance == greater or non-comparable
                        }

                        // if equal, advance both iterators
                        curr_self = self_iter.next();
                        curr_other = other_iter.next();
                    }
                }
                else {
                    // self contains a variable that isn't part of other (& they are equal until now)
                    if self.negative && other.negative {
                        // inverse order
                        return Ordering::Greater;
                    }
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
                    if self.negative && other.negative {
                        // inverse order
                        return Ordering::Less;
                    }
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
        let vir_credit_powers = VirCreditPowers { negative: false, powers };     //TODO: add support for negative annotations

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

    if conditional {
        for (credit_type, opt_cond, abstract_cost) in abstract_credits {
            let credit_type_map: &mut BTreeMap<BTreeSet<VirCreditPowers>, Option<vir::Expr>>
                = result_map.entry(credit_type.clone()).or_default();

            let mut to_remove = vec![];
            let mut to_insert = vec![];       // or overwrite
            // combine new cost with all from before, if results in a new asymptotic cost
            // & add without combination, to generate all possible condition combinations
            for (curr_abstract_cost, curr_opt_cond) in credit_type_map.iter() {
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
    }
    else {
        let mut upper_bounds: HashMap<String, BTreeSet<VirCreditPowers>> = HashMap::new();
        for (credit_type, _opt_cond, abstract_cost) in abstract_credits {
            upper_bounds.entry(credit_type.clone())
                .or_default()
                .extend(abstract_cost.clone());
        }

        for (credit_type, upper_bound) in upper_bounds.drain() {
            let mut condition_map = BTreeMap::new();
            // insert upper bounds without condition
            condition_map.insert(upper_bound, None);
            result_map.insert(credit_type, condition_map);
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

//TODO: move!?
#[derive(Clone, Debug)]
pub(crate) struct CreditConversion {
    pub(crate) credit_type: String,
    pub(crate) result_negative: bool,
    pub(crate) result_exps: Vec<u32>,
    pub(crate) result_bases: Vec<vir::Expr>,
    pub(crate) result_coeff: vir::Expr,
    // above define resulting CreditAccessPredicate expression
    pub(crate) assigned_place_idx: usize,
    pub(crate) conversion_type: CreditConversionType,
}

#[derive(Clone, Debug)]
pub(crate) enum CreditConversionType {
    ConstToPlace {
        constant: vir::Expr,
    },
    Reorder {
        previous_idx: usize,
        previous_base: Option<vir::Expr>,
    },
    SumPlaceConst {
        place_idx: usize,
        place_expr: Option<vir::Expr>,
        const_val: i64,
    },
    MulPlaceConst {
        place_idx: usize,
        place_expr: Option<vir::Expr>,
        const_val: i64,
    },
    DivPlaceConst {     //TODO: summarize with MulPlaceConst
        place_idx: usize,
        place_expr: Option<vir::Expr>,
        const_val: i64,
    },
    SumPlacePlace {
        place1_idx: usize,
        place1_expr: Option<vir::Expr>,
        place2_idx: usize,
        place2_expr: Option<vir::Expr>,
    },
    MulPlacePlace {
        place1_idx: usize,
        place1_expr: Option<vir::Expr>,
        place2_idx: usize,
        place2_expr: Option<vir::Expr>,
    },
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
    conversions: HashMap<mir::Location, Vec<(Option<vir::Expr>, Vec<CreditConversion>)>>,
}

impl PureBackwardSubstitutionState for CostBackwardInterpreterState {
    fn substitute(&mut self, target: &Expr, replacement: Expr, mir_location: mir::Location) -> EncodingResult<()> {

        let mut conditional_conversions = vec![];

        for (opt_condition, credit_cost) in &mut self.cost {
            let mut conversions = vec![];
            for (credit_type, coeff_map) in credit_cost.iter_mut() {
                // coefficients should only contain constants (& abstract coefficient function calls)
                // -> only replace in powers, but cannot directly modify the key!

                // used to avoid modification while iterating over the map, which is not allowed
                let powers_to_replace = coeff_map.keys()
                    .filter(|powers| powers.uses_place(target))
                    .map(|powers| powers.clone())
                    .collect::<Vec<_>>();

                let mut entries_to_replace = vec![];
                for powers in powers_to_replace {
                    let coeff = coeff_map.remove(&powers).unwrap();
                    entries_to_replace.push((powers, coeff));
                }

                if !entries_to_replace.is_empty() {
                    let mut substitute_sum_place_const = |place: &vir::Expr, const_val: i64| {
                        for (mut powers, coeff) in entries_to_replace.clone() {     //TODO: avoid cloning
                            let result_negative = powers.negative;
                            let result_exps = powers.exponents();
                            let result_bases = powers.base_exprs();
                            let result_coeff = coeff.clone();
                            let target_idx = powers.get_index(target);

                            if let Some(exp) = powers.remove_power(target.clone()) {
                                if exp > 66 {
                                    return Err(EncodingError::unsupported(
                                        "Exponents > 66 will lead to an overflow in the cost inference"
                                    ))
                                }

                                let mut const_power = 1i64;
                                // compute binomial expansion of (place + const_val)^exp
                                for i in 0u32..=exp {
                                    let binomial = num_integer::binomial(exp as i64, i as i64);
                                    let mut multiplier = binomial * const_power;
                                    let mut new_powers = powers.clone();
                                    if multiplier < 0 {
                                        new_powers.negative = !powers.negative;
                                        multiplier = -multiplier;   // make coeff/perm amount positive
                                    }
                                    let new_coeff = vir::Expr::mul(multiplier.into(), coeff.clone());

                                    let new_exp = exp - i;
                                    if new_exp > 0u32 {
                                        new_powers.insert_power(place.clone(), new_exp);        //TODO: improve efficiency by not inserting every time, just change exponent/remove
                                    }

                                    // could already have a coefficient for these powers after replacement
                                    // if that is the case, we add the coefficients
                                    if let Some(curr_coeff) = coeff_map.get_mut(&new_powers) {
                                        *curr_coeff = vir::Expr::add(curr_coeff.clone(), new_coeff);
                                    } else {
                                        coeff_map.insert(new_powers, new_coeff);
                                    }

                                    const_power *= const_val;
                                }

                                // insert just to determine index
                                let newly_inserted = powers.insert_power(place.clone(), 1);
                                let insertion_idx = powers.get_index(place).unwrap();
                                let place_expr = if newly_inserted {
                                    Some(place.clone())
                                }
                                else {
                                    None
                                };
                                // insert conversion
                                conversions.push(
                                    CreditConversion {
                                        credit_type: credit_type.clone(),
                                        result_negative,
                                        result_exps,
                                        result_bases,
                                        result_coeff,
                                        assigned_place_idx: target_idx.unwrap(),
                                        conversion_type: CreditConversionType::SumPlaceConst {
                                            place_idx: insertion_idx,
                                            place_expr,
                                            const_val,
                                        }
                                    }
                                );
                            }
                            else {
                                return Err(EncodingError::internal(
                                    format!("Substitution target {} should occur as single expression in base of powers {}", target, powers)
                                ));
                            }
                        }
                        Ok(())
                    };

                    if replacement.is_constant() {
                        // a power is constant -> eliminate from powers & multiply to coefficient
                        for (mut powers, mut coeff) in entries_to_replace {
                            let result_negative = powers.negative;
                            let result_exps = powers.exponents();
                            let result_bases = powers.base_exprs();
                            let result_coeff = coeff.clone();
                            let target_idx = powers.get_index(target);

                            if let Some(exp) = powers.remove_power(target.clone()) {
                                // insert conversion
                                conversions.push(
                                    CreditConversion {
                                        credit_type: credit_type.clone(),
                                        result_negative,
                                        result_exps,
                                        result_bases,
                                        result_coeff,
                                        assigned_place_idx: target_idx.unwrap(),
                                        conversion_type: CreditConversionType::ConstToPlace {
                                            constant: replacement.clone(),
                                        }
                                    }
                                );

                                // multiply coeff^exp with constant
                                for _i in 0..exp {
                                    coeff = vir::Expr::mul(replacement.clone(), coeff);
                                }
                                // could already have a coefficient for these powers after replacement
                                // if that is the case, we add the coefficients
                                if let Some(curr_coeff) = coeff_map.get_mut(&powers) {
                                    *curr_coeff = vir::Expr::add(curr_coeff.clone(), coeff);
                                } else {
                                    coeff_map.insert(powers, coeff);
                                }
                            } else {
                                return Err(EncodingError::internal(
                                    format!("Substitution target {} should occur as single expression in base of powers {}", target, powers)
                                ));
                            }
                        }
                    } else {
                        match &replacement {
                            place @ (Expr::Local(..) | Expr::Field(..))
                            | Expr::SnapApp(box place @ (Expr::Local(..) | Expr::Field(..)), _) => {            //TODO: patch snapApps or use procedure_encoder encoding instead of pure
                                for (mut powers, coeff) in entries_to_replace {
                                    let result_negative = powers.negative;
                                    let result_exps = powers.exponents();
                                    let result_bases = powers.base_exprs();
                                    let result_coeff = coeff.clone();

                                    // replace in base
                                    let (replaced_indices, bases_with_replacement) = powers.replace_place(target, place);
                                    assert_eq!(bases_with_replacement.len(), 1);         //TODO
                                    let target_idx = replaced_indices[0];
                                    let insertion_idx = powers.get_index(&bases_with_replacement[0].0).unwrap();
                                    let previous_base = if bases_with_replacement[0].1 {
                                        Some(bases_with_replacement[0].0.clone())
                                    }
                                    else {
                                        None
                                    };

                                    if target_idx != insertion_idx {    // check if reordering is needed
                                        conversions.push(
                                            CreditConversion {
                                                credit_type: credit_type.clone(),
                                                result_negative,
                                                result_exps,
                                                result_bases,
                                                result_coeff,
                                                assigned_place_idx: target_idx,
                                                conversion_type: CreditConversionType::Reorder {
                                                    previous_idx: insertion_idx,
                                                    previous_base,
                                                }
                                            }
                                        );
                                    }

                                    // could already have a coefficient for these powers after replacement
                                    // if that is the case, we add the coefficients
                                    if let Some(curr_coeff) = coeff_map.get_mut(&powers) {
                                        *curr_coeff = vir::Expr::add(curr_coeff.clone(), coeff);
                                    } else {
                                        coeff_map.insert(powers, coeff);
                                    }
                                }
                            }

                            Expr::BinOp(
                                vir::BinOpKind::Add,
                                box Expr::SnapApp(box vir::Expr::Const(vir::Const::Int(const_val), _), _),
                                box Expr::SnapApp(box place @ (vir::Expr::Local(..) | vir::Expr::Field(..)), _),
                                _,
                            )
                            | Expr::BinOp(
                                vir::BinOpKind::Add,
                                box Expr::SnapApp(box place @ (vir::Expr::Local(..) | vir::Expr::Field(..)), _),
                                box Expr::SnapApp(box vir::Expr::Const(vir::Const::Int(const_val), _), _),
                                _,
                            ) => {  // sum of constant & var
                                substitute_sum_place_const(place, *const_val)?;
                            }

                            Expr::BinOp(
                                vir::BinOpKind::Sub,
                                box Expr::SnapApp(box place @ (vir::Expr::Local(..) | vir::Expr::Field(..)), _),
                                box Expr::SnapApp(box vir::Expr::Const(vir::Const::Int(const_val), _), _),
                                _,
                            ) => {
                                substitute_sum_place_const(place, -*const_val)?;
                            }

                            Expr::BinOp(
                                vir::BinOpKind::Add,
                                box Expr::SnapApp(box place1 @ (vir::Expr::Local(..) | vir::Expr::Field(..)), _),
                                box Expr::SnapApp(box place2 @ (vir::Expr::Local(..) | vir::Expr::Field(..)), _),
                                _,
                            ) => {  // sum of two places
                                for (mut powers, coeff) in entries_to_replace {
                                    let result_negative = powers.negative;
                                    let result_exps = powers.exponents();
                                    let result_bases = powers.base_exprs();
                                    let result_coeff = coeff.clone();
                                    let target_idx = powers.get_index(target);

                                    if let Some(exp) = powers.remove_power(target.clone()) {
                                        if exp > 66 {
                                            return Err(EncodingError::unsupported(
                                                "Exponents > 66 will lead to an overflow in the cost inference"
                                            ))
                                        }

                                        // compute binomial expansion of (place1 + place2)^exp
                                        for i in 0u32..=exp {
                                            let binomial = num_integer::binomial(exp as i64, i as i64);
                                            let new_coeff = vir::Expr::mul(binomial.into(), coeff.clone());

                                            let mut new_powers = powers.clone();
                                            // add place1^i * place2^(exp-i)
                                            let exp2 = exp - i;
                                            if i == 0 {
                                                new_powers.insert_power(place2.clone(), exp2);
                                            } else {
                                                new_powers.insert_power(place1.clone(), i);
                                                if exp2 > 0 {
                                                    new_powers.insert_power(place2.clone(), exp2);
                                                }
                                            }

                                            // could already have a coefficient for these powers after replacement
                                            // if that is the case, we add the coefficients
                                            if let Some(curr_coeff) = coeff_map.get_mut(&new_powers) {
                                                *curr_coeff = vir::Expr::add(curr_coeff.clone(), new_coeff);
                                            } else {
                                                coeff_map.insert(new_powers, new_coeff);
                                            }
                                        }

                                        // insert to determine indices
                                        let newly_inserted1 = powers.insert_power(place1.clone(), 1);
                                        let newly_inserted2 = powers.insert_power(place2.clone(), 1);
                                        let place1_idx = powers.get_index(place1).unwrap();
                                        let place2_idx = powers.get_index(place2).unwrap();
                                        let place1_expr = if newly_inserted1 {
                                            Some(place1.clone())
                                        }
                                        else {
                                            None
                                        };
                                        let place2_expr = if newly_inserted2 {
                                            Some(place2.clone())
                                        }
                                        else {
                                            None
                                        };
                                        // insert conversion
                                        conversions.push(
                                            CreditConversion {
                                                credit_type: credit_type.clone(),
                                                result_negative,
                                                result_exps,
                                                result_bases,
                                                result_coeff,
                                                assigned_place_idx: target_idx.unwrap(),
                                                conversion_type: CreditConversionType::SumPlacePlace {
                                                    place1_idx,
                                                    place1_expr,
                                                    place2_idx,
                                                    place2_expr,
                                                },
                                            }
                                        );
                                    } else {
                                        return Err(EncodingError::internal(
                                            format!("Substitution target {} should occur as single expression in base of powers {}", target, powers)
                                        ));
                                    }
                                }
                            }

                            Expr::BinOp(
                                vir::BinOpKind::Mul,
                                box Expr::SnapApp(box vir::Expr::Const(vir::Const::Int(const_val), _), _),
                                box Expr::SnapApp(box place @ (vir::Expr::Local(..) | vir::Expr::Field(..)), _),
                                _,
                            )
                            | Expr::BinOp(
                                vir::BinOpKind::Mul,
                                box Expr::SnapApp(box place @ (vir::Expr::Local(..) | vir::Expr::Field(..)), _),
                                box Expr::SnapApp(box vir::Expr::Const(vir::Const::Int(const_val), _), _),
                                _,
                            ) => {  // product of constant & place
                                if *const_val < 0 {
                                    return Err(EncodingError::unsupported(
                                        "Multiplications with a negative constant are not supported in the credit cost inference. \
                                        Multiply with a positive constant and subtract afterwards instead."
                                    ));
                                }
                                // just replace target with place & multiply constant to coefficient
                                for (mut powers, mut coeff) in entries_to_replace {
                                    let result_negative = powers.negative;
                                    let result_exps = powers.exponents();
                                    let result_bases = powers.base_exprs();
                                    let result_coeff = coeff.clone();
                                    let target_idx = powers.get_index(target);

                                    if let Some(exp) = powers.remove_power(target.clone()) {
                                        let multiplier = const_val.checked_pow(exp)
                                            .ok_or_else(
                                                || EncodingError::internal(
                                                    format!("Computation of coefficient in cost inference will overflow for {} = {}", target, replacement)
                                                )
                                            )?;
                                        coeff = vir::Expr::mul(multiplier.into(), coeff);

                                        let newly_inserted = powers.insert_power(place.clone(), exp);
                                        let insertion_idx = powers.get_index(place).unwrap();
                                        let place_expr = if newly_inserted {
                                            Some(place.clone())
                                        }
                                        else {
                                            None
                                        };
                                        // insert conversion
                                        conversions.push(
                                            CreditConversion {
                                                credit_type: credit_type.clone(),
                                                result_negative,
                                                result_exps,
                                                result_bases,
                                                result_coeff,
                                                assigned_place_idx: target_idx.unwrap(),
                                                conversion_type: CreditConversionType::MulPlaceConst {
                                                    place_idx: insertion_idx,
                                                    place_expr,
                                                    const_val: *const_val,
                                                },
                                            }
                                        );

                                        // could already have a coefficient for these powers after replacement
                                        // if that is the case, we add the coefficients
                                        if let Some(curr_coeff) = coeff_map.get_mut(&powers) {
                                            *curr_coeff = vir::Expr::add(curr_coeff.clone(), coeff);
                                        } else {
                                            coeff_map.insert(powers, coeff);
                                        }
                                    } else {
                                        return Err(EncodingError::internal(
                                            format!("Substitution target {} should occur as single expression in base of powers {}", target, powers)
                                        ));
                                    }
                                }
                            }

                            Expr::BinOp(
                                vir::BinOpKind::Div,
                                box Expr::SnapApp(box lhs_place @ (vir::Expr::Local(..) | vir::Expr::Field(..)), _),
                                box Expr::SnapApp(box vir::Expr::Const(vir::Const::Int(rhs_const_val), _), _),
                                _
                            ) => {      //TODO: summarize with mul -> times 1/const // differences in Viper?
                                if *rhs_const_val < 0 {
                                    return Err(EncodingError::unsupported(
                                        "Divisions by a negative constant are not supported in the credit cost inference. \
                                        Divide with a positive constant and subtract afterwards instead."
                                    ));
                                }
                                // divide coefficient by const & replace by lhs in powers
                                for (mut powers, mut coeff) in entries_to_replace {
                                    let result_negative = powers.negative;
                                    let result_exps = powers.exponents();
                                    let result_bases = powers.base_exprs();
                                    let result_coeff = coeff.clone();
                                    let target_idx = powers.get_index(target);

                                    if let Some(exp) = powers.remove_power(target.clone()) {
                                        let divisor = rhs_const_val.checked_pow(exp)
                                            .ok_or_else(
                                                || EncodingError::internal(
                                                    format!("Computation of coefficient in cost inference will overflow for {} = {}", target, replacement)
                                                )
                                            )?;
                                        coeff = vir::Expr::div(coeff, divisor.into());

                                        let newly_inserted = powers.insert_power(lhs_place.clone(), exp);
                                        let insertion_idx = powers.get_index(lhs_place).unwrap();
                                        let place_expr = if newly_inserted {
                                            Some(lhs_place.clone())
                                        }
                                        else {
                                            None
                                        };
                                        // insert conversion
                                        conversions.push(
                                            CreditConversion {
                                                credit_type: credit_type.clone(),
                                                result_negative,
                                                result_exps,
                                                result_bases,
                                                result_coeff,
                                                assigned_place_idx: target_idx.unwrap(),
                                                conversion_type: CreditConversionType::DivPlaceConst {
                                                    place_idx: insertion_idx,
                                                    place_expr,
                                                    const_val: *rhs_const_val,
                                                },
                                            }
                                        );

                                        // could already have a coefficient for these powers after replacement
                                        // if that is the case, we add the coefficients
                                        if let Some(curr_coeff) = coeff_map.get_mut(&powers) {
                                            *curr_coeff = vir::Expr::add(curr_coeff.clone(), coeff);
                                        } else {
                                            coeff_map.insert(powers, coeff);
                                        }
                                    } else {
                                        return Err(EncodingError::internal(
                                            format!("Substitution target {} should occur as single expression in base of powers {}", target, powers)
                                        ));
                                    }
                                }
                            }

                            Expr::BinOp(
                                vir::BinOpKind::Mul,
                                box Expr::SnapApp(box place1 @ (vir::Expr::Local(..) | vir::Expr::Field(..)), _),
                                box Expr::SnapApp(box place2 @ (vir::Expr::Local(..) | vir::Expr::Field(..)), _),
                                _,
                            ) => {
                                // replace target by two new places in powers
                                for (mut powers, coeff) in entries_to_replace {
                                    let result_negative = powers.negative;
                                    let result_exps = powers.exponents();
                                    let result_bases = powers.base_exprs();
                                    let result_coeff = coeff.clone();
                                    let target_idx = powers.get_index(target);

                                    if let Some(exp) = powers.remove_power(target.clone()) {
                                        let newly_inserted1 = powers.insert_power(place1.clone(), exp);
                                        let newly_inserted2 = powers.insert_power(place2.clone(), exp);
                                        let insertion_idx1 = powers.get_index(place1).unwrap();
                                        let insertion_idx2 = powers.get_index(place2).unwrap();
                                        let place1_expr = if newly_inserted1 {
                                            Some(place1.clone())
                                        }
                                        else {
                                            None
                                        };
                                        let place2_expr = if newly_inserted2 {
                                            Some(place2.clone())
                                        }
                                        else {
                                            None
                                        };
                                        // insert conversion
                                        conversions.push(
                                            CreditConversion {
                                                credit_type: credit_type.clone(),
                                                result_negative,
                                                result_exps,
                                                result_bases,
                                                result_coeff,
                                                assigned_place_idx: target_idx.unwrap(),
                                                conversion_type: CreditConversionType::MulPlacePlace {
                                                    place1_idx: insertion_idx1,
                                                    place1_expr,
                                                    place2_idx: insertion_idx2,
                                                    place2_expr,
                                                },
                                            }
                                        );

                                        // could already have a coefficient for these powers after replacement
                                        // if that is the case, we add the coefficients
                                        if let Some(curr_coeff) = coeff_map.get_mut(&powers) {
                                            *curr_coeff = vir::Expr::add(curr_coeff.clone(), coeff);
                                        } else {
                                            coeff_map.insert(powers, coeff);
                                        }
                                    } else {
                                        return Err(EncodingError::internal(
                                            format!("Substitution target {} should occur as single expression in base of powers {}", target, powers)
                                        ));
                                    }
                                }
                            }

                            Expr::UnaryOp(vir::UnaryOpKind::Minus, ..) => {
                                return Err(EncodingError::unsupported(
                                    "Negations of places are not supported. Use Subtraction instead."
                                ));
                            }

                            _ => {
                                // TODO: more specific errors per replacement type
                                return Err(EncodingError::unsupported(
                                    format!("Credit costs depending on {:?} are not supported", replacement)
                                ));
                            }
                        }
                    }
                }
            }

            if !conversions.is_empty() {
                conditional_conversions.push((opt_condition.clone(), conversions));
            }
            *opt_condition = opt_condition.as_ref().map(|cond_expr| cond_expr.clone().replace_place(target, &replacement));      //TODO: avoid cloning?
        }

        if !conditional_conversions.is_empty() {
            self.conversions.entry(mir_location)
                .or_default()
                .extend(conditional_conversions);
        }
        Ok(())
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
    pure_fn_interpreter: PureFunctionBackwardInterpreter<'p, 'v, 'tcx>,
    mir_encoder: &'a MirEncoder<'p, 'v, 'tcx>,
    locals_manager: &'a LocalVariableManager<'tcx>,
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

    fn apply_terminator(&self, bb: mir::BasicBlock, terminator: &mir::Terminator<'tcx>, states: HashMap<mir::BasicBlock, &Self::State>) -> Result<Self::State, Self::Error> {
        let term_span = terminator.source_info.span;
        let location = self.mir.terminator_loc(bb);

        trace!("Apply terminator with span {:?};\n\
                states before: {:?}",
                term_span,
                states,
        );

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
                let mut union_of_conversions = HashMap::new();
                let mut guard_disjunction = None;
                for (value, target) in targets.iter() {
                    let target_state = states[&target];
                    // there shouldn't be duplicate keys with different conversions, since locations in different branches should differ
                    union_of_conversions.extend(target_state.conversions.clone());

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
                    self.insert_guarded_cost(&mut new_cost, &target_state.cost, viper_guard);
                }

                let otherwise_guard = vir::Expr::not(guard_disjunction.unwrap());
                let otherwise_state = states[&targets.otherwise()];
                self.insert_guarded_cost(&mut new_cost, &otherwise_state.cost, otherwise_guard);
                union_of_conversions.extend(otherwise_state.conversions.clone());

                let result_state = CostBackwardInterpreterState { cost: new_cost, conversions: union_of_conversions };
                trace!("Result state: {:?}", result_state);
                Ok(result_state)
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

                            trace!(
                                "Function call: def_id '{:?}', contract '{:?}', target_local '{:?}', target_block: '{:?}'",
                                def_id,
                                procedure_contract,
                                target_local,
                                target_block,
                            );

                            let encoded_args: Vec<vir::Expr> = procedure_contract
                                .args
                                .iter()
                                .map(|local| {      // cf. ProcedureEncoder.encode_prusti_local
                                    let var_name = self.locals_manager.get_name(*local);
                                    let type_name = self
                                        .encoder
                                        .encode_type_predicate_use(self.locals_manager.get_type(*local)).unwrap(); // will panic if attempting to encode unsupported type
                                    vir::LocalVar::new(var_name, vir::Type::TypedRef(type_name)).into()
                                })
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

                            trace!("Result state: {:?}", new_state);
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
                trace!(
                    "DropAndReplace target '{:?}', place '{:?}', value '{:?}'",
                    target,
                    lhs,
                    value,
                );
                let mut new_state = states[target].clone();
                new_state.apply_assignment(&self.pure_fn_interpreter, lhs, &mir::Rvalue::Use(value.clone()), location, term_span, self.proc_def_id)?;
                trace!("Result state: {:?}", new_state);
                Ok(new_state)
            }

            TerminatorKind::Assert {
                ref cond,
                expected,
                ref target,
                ..
            } => {
                trace!(
                    "Assert cond '{:?}', expected '{:?}', target '{:?}'",
                    cond,
                    expected,
                    target,
                );

                let target_state = states[target];

                let cond_val = self.mir_encoder.encode_operand_expr(cond)
                    .with_span(term_span)?;
                let viper_guard = if expected {
                    cond_val
                } else {
                    vir::Expr::not(cond_val)
                };

                let mut new_cost = vec![];
                // ignore failure & add condition
                self.insert_guarded_cost(&mut new_cost, &target_state.cost, viper_guard);

                let result_state = CostBackwardInterpreterState { cost: new_cost, conversions: target_state.conversions.clone()};
                trace!("Result state: {:?}", result_state);
                Ok(result_state)
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
                // TODO: error (for some)?
                // no cost
                Ok(CostBackwardInterpreterState { cost: vec![(None, BTreeMap::new())], conversions: HashMap::new() })
            }

            _ => unimplemented!("{:?}", terminator.kind),
        }
    }

    fn apply_statement(&self, bb: mir::BasicBlock, stmt_index: usize, stmt: &mir::Statement<'tcx>, state: &mut Self::State) -> Result<(), Self::Error> {
        let stmt_span = stmt.source_info.span;
        let location = mir::Location {
            block: bb,
            statement_index: stmt_index,
        };

        match stmt.kind {
            mir::StatementKind::Assign(box (ref lhs, ref rhs)) => {
                trace!("State before: {:?}", state);
                trace!("Assign lhs '{:?}', rhs '{:?}'", lhs, rhs);
                state.apply_assignment(&self.pure_fn_interpreter, lhs, rhs, location, stmt_span, self.proc_def_id)?;
                trace!("Result state: {:?}", state);
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