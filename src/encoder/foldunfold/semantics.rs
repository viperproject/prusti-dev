// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::vir;
use encoder::foldunfold::state::*;

impl vir::Stmt {
    pub fn apply_on_state(&self, state: &mut State) {
        match self {
            &vir::Stmt::Comment(_) |
            &vir::Stmt::Label(_) |
            &vir::Stmt::Assert(_, _) => {},

            &vir::Stmt::New(ref var, ref fields) => {
                state.remove_pred_matching(|p| p.base() == var);
                state.remove_acc_matching(|p| !p.is_base() && p.base() == var);
                for field in fields {
                    state.insert_acc(vir::Place::Base(var.clone()).access(field.clone()));
                }
            },

            &vir::Stmt::Inhale(ref expr) => {
                state.insert_all(expr.get_access_places().into_iter());
            },

            &vir::Stmt::Exhale(ref expr, _) => {
                state.remove_all(expr.get_access_places().iter());
            },

            &vir::Stmt::MethodCall(_, _, ref vars) => {
                // We know that in Prusti method's preconditions and postconditions are empty
                state.remove_pred_matching( |p| vars.contains(p.base()));
                state.remove_acc_matching( |p| !p.is_base() && vars.contains(p.base()));
            },

            &vir::Stmt::Assign(ref lhs_place, ref rhs) => {
                let original_state = state.clone();

                // First of all, remove places that will not have a name
                state.remove_pred_matching( |p| p.has_prefix(&lhs_place));
                state.remove_acc_matching( |p| p.has_proper_prefix(&lhs_place));

                // Then, in case of aliasing, add new places
                match rhs {
                    &vir::Expr::Place(ref rhs_place) if rhs_place.get_type().is_ref() => {
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
                    },
                    _ => {}
                }
            },

            &vir::Stmt::Fold(ref _pred_name, ref _args) => {
                unimplemented!()
            },

            &vir::Stmt::Unfold(ref _pred_name, ref _args) => {
                unimplemented!()
            },
        }
    }
}
