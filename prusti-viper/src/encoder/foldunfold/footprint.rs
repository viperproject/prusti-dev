// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::places_utils::{union, union3};
use crate::encoder::foldunfold::perm::Perm::*;
use crate::encoder::foldunfold::perm::*;
use crate::encoder::foldunfold::requirements::*;
use prusti_common::vir;
use prusti_common::vir::PermAmount;
use std::collections::HashMap;
use std::collections::HashSet;
use std::iter::FromIterator;
use log::{trace, debug};

pub trait ExprPermissionsGetter {
    fn get_permissions(&self, predicates: &HashMap<String, vir::Predicate>) -> HashSet<Perm>;
}

impl ExprPermissionsGetter for vir::Expr {
    /// Returns the permissions that must be inhaled/exhaled in a `inhale/exhale expr` statement
    /// This must be a subset of `get_required_permissions`
    fn get_permissions(&self, predicates: &HashMap<String, vir::Predicate>) -> HashSet<Perm> {
        trace!("get_permissions {}", self);
        match self {
            vir::Expr::Local(_, _)
            | vir::Expr::Field(_, _, _)
            | vir::Expr::Variant(_, _, _)
            | vir::Expr::AddrOf(_, _, _)
            | vir::Expr::LabelledOld(_, _, _)
            | vir::Expr::Const(_, _)
            | vir::Expr::FuncApp(..)
            | vir::Expr::DomainFuncApp(..)
            | vir::Expr::InhaleExhale(..) => HashSet::new(),

            vir::Expr::Unfolding(_, args, expr, perm_amount, variant, _) => {
                assert_eq!(args.len(), 1);
                let place = &args[0];
                debug_assert!(place.is_place());

                // We want to temporarly unfold place
                let predicate_name = place.typed_ref_name().unwrap();
                let predicate = predicates.get(&predicate_name).unwrap();

                let pred_self_place: vir::Expr = predicate.self_place();
                let places_in_pred: HashSet<Perm> = predicate
                    .get_permissions_with_variant(variant)
                    .into_iter()
                    .map(|aop| {
                        aop.map_place(|p| p.replace_place(&pred_self_place, place))
                            .init_perm_amount(*perm_amount)
                    })
                    .collect();

                // Simulate temporary unfolding of `place`
                let expr_access_places = expr.get_permissions(predicates);

                // inhaled = inhaled in body - unfolding
                perm_difference(expr_access_places, places_in_pred)
            }

            vir::Expr::UnaryOp(_, ref expr, _) => expr.get_permissions(predicates),

            vir::Expr::BinOp(_, box left, box right, _) => union(
                &left.get_permissions(predicates),
                &right.get_permissions(predicates),
            ),

            vir::Expr::Cond(box guard, box left, box right, _) => union3(
                &guard.get_permissions(predicates),
                &left.get_permissions(predicates),
                &right.get_permissions(predicates),
            ),

            vir::Expr::ForAll(vars, _triggers, box body, _) => {
                assert!(vars.iter().all(|var| !var.typ.is_ref()));
                let vars_places: HashSet<Perm> = vars
                    .iter()
                    .map(|var| Acc(vir::Expr::local(var.clone()), PermAmount::Write))
                    .collect();
                perm_difference(body.get_permissions(predicates), vars_places)
            }

            vir::Expr::PredicateAccessPredicate(_, box ref arg, perm_amount, _) => {
                let opt_perm = if arg.is_place() {
                    Some(match arg.get_label() {
                        None => Perm::Pred(arg.clone(), *perm_amount),
                        Some(label) => Perm::Pred(arg.clone().old(label), *perm_amount),
                    })
                } else {
                    None
                };

                opt_perm.into_iter().collect()
            }

            vir::Expr::FieldAccessPredicate(box ref place, perm_amount, _) => {
                // In Prusti we assume to have only places here
                debug_assert!(place.is_place());
                debug_assert!(place.is_curr());

                let perm = Acc(place.clone(), *perm_amount);

                Some(perm).into_iter().collect()
            }

            vir::Expr::MagicWand(ref _lhs, ref _rhs, _borrow, _) => {
                // We don't track magic wands resources
                HashSet::new()
            }

            vir::Expr::LetExpr(ref _variable, ref _expr, ref _body, _) => {
                unreachable!("Let expressions should be introduced after fold/unfold.");
            }
        }
    }
}

pub trait PredicatePermissionsGetter {
    fn get_permissions_with_variant(
        &self,
        maybe_variant: &vir::MaybeEnumVariantIndex,
    ) -> HashSet<Perm>;
}

impl PredicatePermissionsGetter for vir::Predicate {
    /// Returns the permissions that must be added/removed in a `fold/unfold pred` statement
    fn get_permissions_with_variant(
        &self,
        maybe_variant: &vir::MaybeEnumVariantIndex,
    ) -> HashSet<Perm> {
        let perms = match self {
            vir::Predicate::Struct(p) => {
                assert!(maybe_variant.is_none());
                p.get_permissions()
            }
            vir::Predicate::Enum(p) => {
                if let Some(variant) = maybe_variant {
                    p.get_permissions(variant)
                } else {
                    // We must be doing fold/unfold for a pure function.
                    p.get_all_permissions()
                }
            }
            vir::Predicate::Bodyless(_, _) => HashSet::new(),
        };
        perms
    }
}

pub trait StructPredicatePermissionsGetter {
    fn get_permissions(&self) -> HashSet<Perm>;
}

impl StructPredicatePermissionsGetter for vir::StructPredicate {
    /// Returns the permissions that must be added/removed in a `fold/unfold pred` statement
    fn get_permissions(&self) -> HashSet<Perm> {
        match self.body {
            Some(ref body) => {
                // A predicate body should not contain unfolding expression
                let predicates = HashMap::new();
                body.get_permissions(&predicates)
            }
            None => HashSet::new(),
        }
    }
}

pub trait EnumPredicatePermissionsGetter {
    fn get_permissions(&self, variant: &vir::EnumVariantIndex) -> HashSet<Perm>;
    fn get_all_permissions(&self) -> HashSet<Perm>;
}

impl EnumPredicatePermissionsGetter for vir::EnumPredicate {
    /// Returns the permissions that must be added/removed in a `fold/unfold pred` statement
    fn get_permissions(&self, variant: &vir::EnumVariantIndex) -> HashSet<Perm> {
        // A predicate body should not contain unfolding expression
        let predicates = HashMap::new();
        let mut perms = self.discriminant.get_required_permissions(&predicates);
        let this: vir::Expr = self.this.clone().into();
        //let (_, ref variant_name, _) = &self.variants[variant];
        let variant_name = variant.get_variant_name();
        perms.insert(Perm::Acc(
            this.clone().variant(variant_name),
            PermAmount::Write,
        ));
        perms.insert(Perm::Pred(
            this.clone().variant(variant_name),
            PermAmount::Write,
        ));
        perms
    }

    /// Returns the permissions that must be added/removed in a `fold/unfold pred` statement
    fn get_all_permissions(&self) -> HashSet<Perm> {
        // A predicate body should not contain unfolding expression
        let predicates = HashMap::new();
        let mut perms = self.discriminant.get_required_permissions(&predicates);
        let this: vir::Expr = self.this.clone().into();
        for (_guard, variant_name, _variant_predicate) in &self.variants {
            perms.insert(Perm::Acc(
                this.clone().variant(&variant_name),
                PermAmount::Write,
            ));
            perms.insert(Perm::Pred(
                this.clone().variant(&variant_name),
                PermAmount::Write,
            ));
        }
        perms
    }
}
