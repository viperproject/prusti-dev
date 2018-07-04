// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::foldunfold::perm::*;
use encoder::foldunfold::state::*;
use encoder::vir;
use std::collections::HashMap;

impl vir::Stmt {
    pub fn apply_on_state(&self, state: &mut State, predicates: &HashMap<String, vir::Predicate>) {
        debug!("apply_on_state '{}'", self);
        trace!("State acc {{{}}}", state.display_acc());
        trace!("State pred {{{}}}", state.display_pred());
        trace!("State moved {{{}}}", state.display_moved());
        match self {
            &vir::Stmt::Comment(_) |
            &vir::Stmt::Label(_) |
            &vir::Stmt::Assert(_, _) |
            &vir::Stmt::Obtain(_) => {},

            &vir::Stmt::Inhale(ref expr) => {
                state.insert_all_perms(expr.get_access_places(predicates).into_iter());
            },

            &vir::Stmt::Exhale(ref expr, _) => {
                state.remove_all_perms(expr.get_access_places(predicates).iter());
            },

            &vir::Stmt::MethodCall(_, _, ref targets) => {
                // We know that in Prusti method's preconditions and postconditions are empty
                state.remove_moved_matching( |p| targets.contains(p.base()));
                state.remove_pred_matching( |p| targets.contains(p.base()));
                state.remove_acc_matching( |p| !p.is_base() && targets.contains(p.base()));
            },

            &vir::Stmt::Assign(ref lhs_place, ref rhs) => {
                let original_state = state.clone();

                // First of all, remove places that will not have a name
                state.remove_moved_matching( |p| p.has_prefix(&lhs_place));
                state.remove_pred_matching( |p| p.has_prefix(&lhs_place));
                state.remove_acc_matching( |p| p.has_proper_prefix(&lhs_place));

                // Then, in case of aliasing, add new places
                match rhs {
                    &vir::Expr::Place(ref rhs_place) if rhs_place.get_type().is_ref() => {
                        // This is the encoding of a move assignemnt

                        // Check that the rhs contains no moved paths
                        assert!(!state.is_prefix_of_some_moved(&rhs_place));
                        for prefix in rhs_place.all_proper_prefixes() {
                            assert!(!state.contains_pred(prefix));
                        }

                        // In Prusti, we lose permission on the rhs
                        state.remove_pred_matching( |p| p.has_prefix(&rhs_place));
                        state.remove_acc_matching( |p| p.has_proper_prefix(&rhs_place));

                        // And we create permissions for the lhs
                        let new_acc_places = original_state.acc().iter()
                            .filter(|p| p.has_prefix(&rhs_place))
                            .cloned()
                            .map(|p| p.replace_prefix(&rhs_place, lhs_place.clone()));
                        state.insert_all_acc(new_acc_places);

                        let new_pred_places = original_state.pred().iter()
                            .filter(|p| p.has_prefix(&rhs_place))
                            .cloned()
                            .map(|p| p.replace_prefix(&rhs_place, lhs_place.clone()));
                        state.insert_all_pred(new_pred_places);

                        // Finally, mark the rhs as moved
                        state.insert_moved(rhs_place.clone());
                    },
                    _ => {}
                }
            },

            &vir::Stmt::Fold(ref pred_name, ref args) => {
                assert_eq!(args.len(), 1);
                let place = &args[0].clone().as_place().unwrap();
                assert!(!state.contains_pred(&place));
                assert!(!state.is_prefix_of_some_moved(&place));

                // We want to fold place
                let predicate_name = place.typed_ref_name().unwrap();
                let predicate = predicates.get(&predicate_name).unwrap();

                let pred_self_place: vir::Place = predicate.args[0].clone().into();
                let places_in_pred: Vec<Perm> = predicate.get_contained_places().into_iter()
                    .map( |aop| aop.map( |p|
                        p.replace_prefix(&pred_self_place, place.clone())
                    )).collect();

                // Commented due to the presence of implications in the body of predicates
                //for contained_place in &places_in_pred {
                //    assert!(state.contains(contained_place));
                //}

                // Simulate folding of `place`
                state.remove_all_perms(places_in_pred.iter());
                state.insert_pred(place.clone());
            },

            &vir::Stmt::Unfold(ref pred_name, ref args) => {
                assert_eq!(args.len(), 1);
                let place = &args[0].clone().as_place().unwrap();
                assert!(state.contains_pred(&place));
                assert!(!state.is_prefix_of_some_moved(&place));

                // We want to unfold place
                let predicate_name = place.typed_ref_name().unwrap();
                let predicate = predicates.get(&predicate_name).unwrap();

                let pred_self_place: vir::Place = predicate.args[0].clone().into();
                let places_in_pred: Vec<Perm> = predicate.get_contained_places().into_iter()
                    .map( |aop| aop.map( |p|
                        p.replace_prefix(&pred_self_place, place.clone())
                    )).collect();

                for contained_place in &places_in_pred {
                    assert!(!state.contains_perm(contained_place));
                }

                // Simulate unfolding of `place`
                state.remove_pred(&place);
                state.insert_all_perms(places_in_pred.into_iter());
            },
        }
    }
}
