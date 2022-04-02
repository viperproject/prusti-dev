// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::{
    places_utils::{union, union3},
    Predicates,
};
use crate::encoder::foldunfold::perm::{Perm::*, *};
use log::trace;
use rustc_hash::{FxHashMap, FxHashSet};

use vir_crate::polymorphic::{self as vir, PermAmount};

pub trait ExprFootprintGetter {
    /// Returns the precise footprint of an expression, that is the permissions that must be
    /// added/removed when executing an `inhale/exhale expr` statement.
    fn get_footprint(&self, predicates: &Predicates) -> FxHashSet<Perm>;
}

impl ExprFootprintGetter for vir::Expr {
    fn get_footprint(&self, predicates: &Predicates) -> FxHashSet<Perm> {
        trace!("get_footprint {}", self);
        let res = match self {
            vir::Expr::Local(_)
            | vir::Expr::Field(_)
            | vir::Expr::Variant(_)
            | vir::Expr::AddrOf(_)
            | vir::Expr::LabelledOld(_)
            | vir::Expr::Const(_)
            | vir::Expr::FuncApp(_)
            | vir::Expr::DomainFuncApp(_)
            | vir::Expr::InhaleExhale(_) => FxHashSet::default(),

            vir::Expr::Unfolding(vir::Unfolding {
                arguments,
                base,
                permission,
                variant,
                ..
            }) => {
                assert_eq!(arguments.len(), 1);
                let place = &arguments[0];
                debug_assert!(place.is_place());

                // We want to temporarly unfold place
                let predicate_type = place.get_type();
                let predicate = predicates.get(predicate_type).unwrap();

                let pred_self_place: vir::Expr = predicate.self_place();
                let places_in_pred: FxHashSet<Perm> = predicate
                    .get_body_footprint(variant)
                    .into_iter()
                    .map(|aop| {
                        aop.map_place(|p| p.replace_place(&pred_self_place, place))
                            .init_perm_amount(*permission)
                    })
                    .collect();

                // Simulate temporary unfolding of `place`
                let expr_access_places = base.get_footprint(predicates);

                // inhaled = inhaled in body - unfolding
                perm_difference(expr_access_places, places_in_pred)
            }

            vir::Expr::UnaryOp(vir::UnaryOp { argument, .. }) => argument.get_footprint(predicates),

            vir::Expr::BinOp(vir::BinOp {
                box left,
                box right,
                ..
            }) => union(
                &left.get_footprint(predicates),
                &right.get_footprint(predicates),
            ),

            vir::Expr::ContainerOp(vir::ContainerOp {
                box left,
                box right,
                ..
            }) => union(
                &left.get_footprint(predicates),
                &right.get_footprint(predicates),
            ),

            vir::Expr::Seq(vir::Seq { elements, .. }) => elements
                .iter()
                .map(|e| e.get_footprint(predicates))
                .fold(FxHashSet::default(), |mut hs, fp| {
                    hs.extend(fp);
                    hs
                }),

            vir::Expr::Map(vir::Map { elements, .. }) => elements
                .iter()
                .map(|e| e.get_footprint(predicates))
                .fold(FxHashSet::default(), |mut hs, fp| {
                    hs.extend(fp);
                    hs
                }),

            vir::Expr::Cond(vir::Cond {
                box guard,
                box then_expr,
                box else_expr,
                ..
            }) => union3(
                &guard.get_footprint(predicates),
                &then_expr.get_footprint(predicates),
                &else_expr.get_footprint(predicates),
            ),

            vir::Expr::ForAll(vir::ForAll {
                variables,
                box body,
                ..
            })
            | vir::Expr::Exists(vir::Exists {
                variables,
                box body,
                ..
            }) => {
                let vars_places: FxHashSet<Perm> = variables
                    .iter()
                    .map(|var| Acc(vir::Expr::local(var.clone()), PermAmount::Write))
                    .collect();
                perm_difference(body.get_footprint(predicates), vars_places)
            }

            vir::Expr::PredicateAccessPredicate(vir::PredicateAccessPredicate {
                box ref argument,
                permission,
                ..
            }) => {
                let opt_perm = if argument.is_place() {
                    Some(match argument.get_label() {
                        None => Perm::Pred(argument.clone(), *permission),
                        Some(label) => Perm::Pred(argument.clone().old(label), *permission),
                    })
                } else {
                    None
                };

                opt_perm.into_iter().collect()
            }

            vir::Expr::FieldAccessPredicate(vir::FieldAccessPredicate {
                box ref base,
                permission,
                ..
            }) => {
                // In Prusti we assume to have only places here
                debug_assert!(base.is_place());
                debug_assert!(base.is_curr());

                let perm = Acc(base.clone(), *permission);

                Some(perm).into_iter().collect()
            }

            vir::Expr::MagicWand(_) => {
                // We don't track magic wands resources
                FxHashSet::default()
            }

            vir::Expr::LetExpr(_) => {
                unreachable!("Let expressions should be introduced after fold/unfold.");
            }

            vir::Expr::Downcast(vir::DowncastExpr { ref base, .. }) => {
                base.get_footprint(predicates)
            }

            vir::Expr::SnapApp(vir::SnapApp { ref base, .. }) => base.get_footprint(predicates),

            vir::Expr::Cast(vir::Cast { ref base, .. }) => base.get_footprint(predicates),
        };
        trace!("get_footprint {} = {:?}", self, res);
        res
    }
}

pub trait PredicateFootprintGetter {
    /// Returns the footprint of the body of a predicate, that is the permissions that must be
    /// added/removed when executing a `fold/unfold pred` statement.
    /// When the method is called on a predicate encoding an enumeration and `maybe_variant` is
    /// `None` then the result is an under-approximation. The result is precise in all other cases.
    fn get_body_footprint(&self, maybe_variant: &vir::MaybeEnumVariantIndex) -> FxHashSet<Perm>;
}

impl PredicateFootprintGetter for vir::Predicate {
    fn get_body_footprint(&self, maybe_variant: &vir::MaybeEnumVariantIndex) -> FxHashSet<Perm> {
        match self {
            vir::Predicate::Struct(p) => {
                assert!(maybe_variant.is_none());
                p.get_body_footprint()
            }
            vir::Predicate::Enum(p) => {
                if let Some(variant) = maybe_variant {
                    p.get_body_footprint(variant)
                } else {
                    // This case happens when Prusti unfolds an enumeration without statically
                    // knowing the variant. For example, when encoding the lookup of a
                    // discriminant *before* entering a match expression.
                    // Under-approximating is better than over-approximating because it preserves
                    // the invariant that permissions in the fold-unfold state are an
                    // under-approximation of the permissions actually available in Viper.
                    p.get_underapproximated_body_footprint()
                }
            }
            vir::Predicate::Bodyless(_, _) => FxHashSet::default(),
        }
    }
}

pub trait StructPredicateFootprintGetter {
    /// Returns the footprint of the body of a predicate encoding a structure, that is the
    /// permissions that must be added/removed when executing a `fold/unfold pred` statement.
    fn get_body_footprint(&self) -> FxHashSet<Perm>;
}

impl StructPredicateFootprintGetter for vir::StructPredicate {
    fn get_body_footprint(&self) -> FxHashSet<Perm> {
        match self.body {
            Some(ref body) => {
                // A predicate body should not contain unfolding expression
                let predicates = FxHashMap::default();
                body.get_footprint(&predicates)
            }
            None => FxHashSet::default(),
        }
    }
}

pub trait EnumPredicateFootprintGetter {
    /// Returns the footprint of the body of a predicate encoding an enumeration, that is the
    /// permissions that must be added/removed when executing a `fold/unfold pred` statement.
    fn get_body_footprint(&self, variant: &vir::EnumVariantIndex) -> FxHashSet<Perm>;

    /// Returns the footprint coontribution of a given variant of an enumeration.
    fn get_variant_footprint(&self, variant: &vir::EnumVariantIndex) -> FxHashSet<Perm>;

    /// Returns the intersection of `get_body_footprint` called on each possible variant.
    fn get_underapproximated_body_footprint(&self) -> FxHashSet<Perm>;
}

impl EnumPredicateFootprintGetter for vir::EnumPredicate {
    fn get_body_footprint(&self, variant: &vir::EnumVariantIndex) -> FxHashSet<Perm> {
        let mut perms = self.get_underapproximated_body_footprint();
        perms.extend(self.get_variant_footprint(variant));
        perms
    }

    fn get_variant_footprint(&self, variant: &vir::EnumVariantIndex) -> FxHashSet<Perm> {
        let mut perms = FxHashSet::default();
        let this: vir::Expr = self.this.clone().into();
        let variant_name = variant.get_variant_name();
        perms.insert(Perm::Acc(
            this.clone().variant(variant_name),
            PermAmount::Write,
        ));
        perms.insert(Perm::Pred(this.variant(variant_name), PermAmount::Write));
        perms
    }

    fn get_underapproximated_body_footprint(&self) -> FxHashSet<Perm> {
        let mut perms = FxHashSet::default();
        perms.insert(Perm::Acc(
            vir::Expr::from(self.this.clone()).field(self.discriminant_field.clone()),
            PermAmount::Write,
        ));
        perms
    }
}
