// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc_hir::def_id::DefId;
use std::collections::HashSet;

use vir_crate::polymorphic::{self as polymorphic_vir, ExprIterator, WithIdentifier};
use prusti_interface::environment::borrowck::facts::Loan;
use crate::encoder::encoder::Encoder;
use std::collections::HashMap;

const MIRROR_DOMAIN_NAME: &str = "MirrorDomain";

pub struct MirrorEncoder {
    domain: polymorphic_vir::Domain,
    encoded: HashSet<DefId>,
}

// mirror_caller_functions: RefCell<Vec<vir::Function>>

impl MirrorEncoder {
    pub fn new() -> Self {
        Self {
            domain: polymorphic_vir::Domain {
                name: MIRROR_DOMAIN_NAME.to_string(),
                functions: vec![],
                axioms: vec![],
                type_vars: vec![],
            },
            encoded: HashSet::new(),
        }
    }


    pub fn get_domain(&self) -> Option<&polymorphic_vir::Domain> {
        if self.encoded.is_empty() {
            None
        } else {
            Some(&self.domain)
        }
    }

    pub fn encode_mirrors(
        &mut self,
        // encoder: &Encoder,
        def_id: DefId,
        function: &mut polymorphic_vir::Function,
    ) {
        // don't encode a mirror for the same DefId multiple times
        if self.encoded.contains(&def_id) {
            return;
        }
        self.encoded.insert(def_id);

        self.encode_mirror_simple(def_id, function);
        self.encode_mirror_axiomatized(def_id, function);
    }

    fn encode_mirror_simple(
        &mut self,
        _def_id: DefId,
        function: &mut polymorphic_vir::Function,
    ) {
        // create mirror function
        let mirror_func = polymorphic_vir::DomainFunc {
            name: format!("mirror_simple${}", function.name),
            formal_args: function.formal_args.clone(),
            return_type: function.return_type.clone(),
            unique: false,
            domain_name: MIRROR_DOMAIN_NAME.to_string(),
        };

        // add postcondition to the original function
        // [result == mirror(args), true]
        function.posts.push(polymorphic_vir::Expr::InhaleExhale( polymorphic_vir::InhaleExhale {
            inhale_expr: box polymorphic_vir::Expr::eq_cmp(
                polymorphic_vir::Expr::local(
                    polymorphic_vir::LocalVar::new("__result", function.return_type.clone()),
                ),
                polymorphic_vir::Expr::domain_func_app(
                    mirror_func.clone(),
                    function.formal_args.iter()
                        .cloned()
                        .map(polymorphic_vir::Expr::local)
                        .collect(),
                ),
            ),
            exhale_expr: box true.into(),
            position: polymorphic_vir::Position::default(),
        }));

        // add mirror function to mirror domain
        self.domain.functions.push(mirror_func);
    }

    // TODO: ...
    fn encode_mirror_axiomatized(
        &mut self,
        _def_id: DefId,
        _function: &mut polymorphic_vir::Function,
    ) {}
}

// ------------------------------
// --- OLD ----------------------
// ------------------------------

/*
pub fn encode_mirror_of_pure_function(
    encoder: &Encoder,
    mirror_function_domain: &mut vir::Domain,
    function: &vir::Function,
) {
    /*
    let snapshots: &HashMap<String, Box<Snapshot>> = &encoder.get_snapshots();
    let formal_args_without_nat: Vec<vir::LocalVar> =
        snapshot::encode_mirror_function_args_without_nat(&function.formal_args, &snapshots).unwrap();

    let domain_function =
        snapshot::encode_mirror_function(&function.name, &function.formal_args, &function.return_type, &snapshots).unwrap();
    let nat_arg = vir::Expr::local(snapshot::encode_nat_argument());
    let nat_succ = vir::Expr::domain_func_app(snapshot::get_succ_func(), vec![nat_arg.clone()]);
    let args_without_nat: Vec<vir::Expr> = formal_args_without_nat
        .clone()
        .into_iter()
        .map(vir::Expr::local)
        .collect();

    let mut args_with_succ = args_without_nat.clone();
    args_with_succ.push(nat_succ);

    let function_call_with_succ = vir::Expr::domain_func_app(domain_function.clone(), args_with_succ.clone());

    let mut args_with_zero = args_without_nat.clone();
    args_with_zero.push(vir::Expr::domain_func_app(snapshot::get_zero_func(), Vec::new()));

    let function_call_with_zero = vir::Expr::domain_func_app(domain_function.clone(), args_with_zero.clone());

    let mut purifier = snapshot::ExprPurifier::new(&snapshots, snapshot::encode_nat_argument().into());
    purifier.self_function(Some(function_call_with_succ.clone()));

    let pre_conds: vir::Expr = function
        .pres
        .iter()
        .cloned()
        .map(|p| vir::ExprFolder::fold(&mut purifier, p))
        .conjoin();
    let post_conds: vir::Expr = function
        .posts
        .iter()
        .cloned()
        .filter_map(|p| {
                // Skip the post condition that it is only there to clarify the relation between the result of this function and the (old) mirror fucntion
                // FIXME: This is not at all the correct way to detect this
            if p.to_string().contains("mirror$"){
                None
            } else {
                Some(vir::ExprFolder::fold(&mut purifier, p))
            }
        })
        .conjoin();

    let mut triggers: Vec<vir::Trigger> = formal_args_without_nat
        .iter()
        .filter_map(|arg| match &arg.typ {
            vir::Type::Domain(arg_domain_name) => {
                let self_arg = vir::Expr::local(arg.clone());
                let unfold_func = snapshot::encode_unfold_witness(arg_domain_name.clone());
                let unfold_call =
                    vir::Expr::domain_func_app(unfold_func, vec![self_arg, nat_arg.clone()]);
                Some(unfold_call)
            }
            _ => None,
        })
        .map(|t| vir::Trigger::new(vec![t, function_call_with_zero.clone()]))
        .collect();

    triggers.push(vir::Trigger::new(vec![function_call_with_succ.clone()]));

    encode_mirror_caller(encoder, domain_function.clone(), pre_conds.clone());
    encode_definitional_axiom(
        &mut purifier,
        mirror_function_domain,
        &function,
        domain_function.clone(),
        formal_args_without_nat.clone(),
        function_call_with_succ.clone(),
        pre_conds,
        post_conds,
        triggers.clone(),
    );
    encode_nat_axiom(
        mirror_function_domain,
        &function,
        domain_function.clone(),
        formal_args_without_nat,
        function_call_with_succ,
        triggers);
    mirror_function_domain
        .functions
        .push(domain_function);
    */

}

/// Encode the axiom that defines what the function does.
fn encode_definitional_axiom(
    //purifier: &mut snapshot::ExprPurifier,
    mirror_function_domain: &mut vir::Domain,
    function: &vir::Function,
    domain_function: vir::DomainFunc,
    formal_args_without_nat: Vec<vir::LocalVar>,
    function_call_with_succ: vir::Expr,
    pre_conds: vir::Expr,
    post_conds: vir::Expr,
    triggers: Vec<vir::Trigger>,
) {
    /*
    let rhs: vir::Expr = if let Some(fbody) = function.body.clone() {
        let function_body = vir::ExprFolder::fold(purifier, fbody);

        let function_identity = vir::Expr::eq_cmp(function_call_with_succ, function_body);
        vir::Expr::and(post_conds, function_identity)
    }
    else {
        post_conds
    };
    let valids_anded: vir::Expr = formal_args_without_nat
        .iter()
        .map(|e| {
            let valid_function = snapshot::valid_func_for_type(&e.typ);
            let self_arg = vir::Expr::local(e.clone());
            vir::Expr::domain_func_app(valid_function, vec![self_arg])
        })
        .conjoin();
    let pre_conds_and_valid = vir::Expr::and(pre_conds, valids_anded);
    let axiom_body = vir::Expr::implies(pre_conds_and_valid, rhs);
    let definitional_axiom = vir::DomainAxiom {
        name: format!("{}$axiom", function.get_identifier()),
        expr: vir::Expr::forall(domain_function.formal_args.clone(), triggers.clone(), axiom_body),
        domain_name: mirror_function_domain.name.clone(),
    };
    mirror_function_domain
    .axioms
    .push(definitional_axiom);
    */
}

/// Encode the axiom that the last argument `count` of the function does not
/// influence its value.
fn encode_nat_axiom(
    mirror_function_domain: &mut vir::Domain,
    function: &vir::Function,
    domain_function: vir::DomainFunc,
    formal_args_without_nat: Vec<vir::LocalVar>,
    function_call_with_succ: vir::Expr,
    triggers: Vec<vir::Trigger>,
) {
    /*
    let mut args_without_succ: Vec<vir::Expr> = formal_args_without_nat
        .into_iter()
        .map(vir::Expr::local)
        .collect();
    args_without_succ.push(vir::Expr::local(snapshot::encode_nat_argument()));
    let formal_args = domain_function.formal_args.clone();
    let function_call_without_succ = vir::Expr::domain_func_app(domain_function, args_without_succ);
    let axiom_body = vir::Expr::eq_cmp(function_call_without_succ, function_call_with_succ);
    let axiom = vir::DomainAxiom {
        name: format!("{}$nat_axiom", function.get_identifier()),
        expr: vir::Expr::forall(formal_args, triggers.clone(), axiom_body),
        domain_name: mirror_function_domain.name.clone(),
    };
    mirror_function_domain
    .axioms
    .push(axiom);
    */
}

fn encode_mirror_caller(encoder: &Encoder, df: vir::DomainFunc, pres: vir::Expr) {
    /*
    let arg_call : Vec<vir::Expr> = df.formal_args.iter().map(|e| { vir::Expr::local(e.clone()) }).collect();
    let function = vir::Function {
        name: snapshot::caller_function_name(&df.name),
        formal_args: df.formal_args.clone(),
        return_type: df.return_type.clone(),
        pres: vec![pres],
        posts: vec![],
        body: Some(vir::Expr::domain_func_app(df.clone(), arg_call))
    };
    encoder.insert_mirror_caller(function);
    */
}
*/
