// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

mod places;

use std::collections::HashSet;
use std::collections::HashMap;
use encoder::vir;
use std::iter::FromIterator;
use encoder::vir::utils::ExprIterator;

pub use self::places::*;

pub fn add_fold_unfold(cfg: vir::CfgMethod, predicates: HashMap<String, vir::Predicate>) -> vir::CfgMethod {
    let cfg_vars = cfg.get_all_vars();
    let initial_bctxt = BranchCtxt::new(cfg_vars, predicates);
    cfg.augment(FoldUnfold::new(initial_bctxt))
}

#[derive(Debug, Clone)]
struct BranchCtxt {
    /// This state contains the places `p` such that:
    /// 1. Viper holds an access permission on `p`;
    /// 2. for any other place `q` such that `p` is a prefix of `q`, Viper holds no permission on
    ///    `q`;
    /// 3. if there exist another place `q` such that `p` is a prefix of `q`, Viper holds the type
    ///    predicate of `p` applied on `p`.
    ///
    /// As a corollary, for any place `p` in `state`, for any other place `q` such that `q` is a
    /// prefix of `p`:
    /// 1. Viper holds an access permission on `q` and `q` is *not* in `state`;
    /// 2. Viper does *not* hold the full type predicate of `q` applied on `q`.
    ///
    /// From another point of view, `state` contains the boundary of the path-tree of permission
    /// held in the current Viper state.
    state: HashSet<vir::Place>,
    /// The definition of the predicates
    predicates: HashMap<String, vir::Predicate>
}

impl BranchCtxt {
    pub fn new(local_vars: Vec<vir::LocalVar>, predicates: HashMap<String, vir::Predicate>) -> Self {
        BranchCtxt {
            state: HashSet::from_iter(local_vars.into_iter().map(|v| vir::Place::Base(v))),
            predicates
        }
    }

    fn state_as_vir_expr(&self) -> vir::Expr {
        let mut exprs: Vec<vir::Expr> = vec![];

        for place in &self.state {
            if place.is_base() {
                let pred_name = place.typed_ref_name().unwrap();
                exprs.push(
                    vir::Expr::PredicateAccessPredicate(
                        box vir::Expr::PredicateAccess(pred_name, vec![ place.clone().into() ]),
                        vir::Perm::full()
                    )
                );
            } else {
                exprs.push(
                    vir::Expr::FieldAccessPredicate(
                        box place.clone().into(),
                        vir::Perm::full()
                    )
                );
                if let Some(pred_name) = place.typed_ref_name() {
                    exprs.push(
                        vir::Expr::PredicateAccessPredicate(
                            box vir::Expr::PredicateAccess(pred_name, vec![ place.clone().into() ]),
                            vir::Perm::full()
                        )
                    );
                }
            }
        }

        exprs.into_iter().conjoin()
    }

    fn obtain(&mut self, mut wanted_places: Vec<vir::Place>) -> Vec<vir::Stmt> {
        if wanted_places.is_empty() {
            // Nothing to do
            return vec![];
        }

        debug!("State: {{{}}}", self.state.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", "));
        debug!("Wanted places: {{{}}}", wanted_places.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", "));

        let wanted_place = wanted_places.pop().unwrap();
        if self.state.contains(&wanted_place) {
            // We already have the wanted_place
            debug!("We already have {}. Let us look at the remaining wanted_places", wanted_place);
            return self.obtain(wanted_places);
        }

        // Find a prefix of Place
        let mut existing_prefix: Option<vir::Place> = None;
        for existing_place in &self.state {
            if wanted_place.has_prefix(existing_place) {
                existing_prefix = Some(existing_place.clone());
            }
        }

        let mut stmts: Vec<vir::Stmt> = vec![];
        if let Some(place) = existing_prefix {
            // We want to unfold
            debug!("We want to unfold {:?}", place);
            let predicate_name = place.typed_ref_name().unwrap();
            let predicate = self.predicates.get(&predicate_name).unwrap();
            // Unfold predicate
            stmts.push(
                vir::Stmt::Unfold(predicate.name.clone(), vec![ place.clone().into() ])
            );
            // Apply unfold to state
            assert!(self.state.contains(&place));
            self.state.remove(&place);
            let pred_self_place: vir::Place = predicate.args[0].clone().into();
            let pred_perms: Vec<vir::Place> = predicate.get_contained_places().into_iter()
                .map(|p| p.replace_prefix(&pred_self_place, place.clone()))
                .collect();
            for pred_place in pred_perms {
                self.state.insert(pred_place.clone());
            }
            // Recursive call
            wanted_places.push(wanted_place);
            stmts.append(&mut self.obtain(wanted_places));
        } else {
            // We want to fold
            debug!("We want to fold {:?}", wanted_place);
            let predicate_name = wanted_place.typed_ref_name().unwrap();
            let predicate = self.predicates.get(&predicate_name).unwrap().clone();
            // Prepare to fold
            let pred_self_place: vir::Place = predicate.args[0].clone().into();
            let pred_perms: Vec<vir::Place> = predicate.get_contained_places().into_iter()
                .map(|p| p.replace_prefix(&pred_self_place, wanted_place.clone()))
                .collect();
            stmts.append(&mut self.obtain(pred_perms.iter().cloned().collect()));
            // Fold predicate
            stmts.push(
                vir::Stmt::Fold(predicate.name.clone(), vec![ wanted_place.clone().into() ])
            );
            // Apply fold to state
            self.state.insert(wanted_place);
            for pred_place in pred_perms {
                assert!(self.state.contains(&pred_place));
                self.state.remove(&pred_place);
            }
            // Recursive call
            stmts.append(&mut self.obtain(wanted_places));
        }
        stmts
    }

    pub fn apply_stmt(&mut self, stmt: &vir::Stmt) -> Vec<vir::Stmt> {
        debug!("Apply stmt: {}", stmt);
        let required_places: Vec<vir::Place> = stmt.get_required_places().into_iter().collect();

        let mut stmts: Vec<vir::Stmt> = vec![];

        stmts.push(
            vir::Stmt::comment(format!(
                "Permissions: {{{}}}",
                self.state.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", ")
            ))
        );
        stmts.push(
            vir::Stmt::Assert(self.state_as_vir_expr(), vir::Id())
        );

        let mut new_stmts = self.obtain(required_places);
        let new_stmts_is_empty = new_stmts.is_empty();

        stmts.append(
            &mut new_stmts
        );

        if !new_stmts_is_empty {
            stmts.push(
                vir::Stmt::comment(format!(
                    "Permissions: {{{}}}",
                    self.state.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", ")
                ))
            );
            stmts.push(
                vir::Stmt::Assert(self.state_as_vir_expr(), vir::Id())
            );
        }

        self.state = stmt.get_resulting_places(&self.state);

        debug!("Final state: {{{}}}", self.state.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", "));
        stmts
    }


    pub fn apply_successor(&mut self, succ: &vir::Successor) -> Vec<vir::Stmt> {
        debug!("Apply succ: {:?}", succ);
        let exprs: Vec<&vir::Expr> = match succ {
            &vir::Successor::GotoSwitch(ref guarded_targets, _) => {
                guarded_targets.iter().map(|g| &g.0).collect()
            },
            &vir::Successor::GotoIf(ref expr, _, _) => vec![expr],
            _ => vec![]
        };

        let mut stmts: Vec<vir::Stmt> = vec![];

        stmts.push(
            vir::Stmt::comment(format!(
                "Permissions: {{{}}}",
                self.state.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", ")
            ))
        );
        stmts.push(
            vir::Stmt::Assert(self.state_as_vir_expr(), vir::Id())
        );

        stmts.append(
            &mut self.obtain(
                exprs.iter().flat_map(
                    |e| e.get_required_places().into_iter().collect::<Vec<vir::Place>>()
                ).collect()
            )
        );

        stmts.push(
            vir::Stmt::comment(format!(
                "Permissions: {{{}}}",
                self.state.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", ")
            ))
        );

        stmts
    }
}

#[derive(Debug, Clone)]
struct FoldUnfold {
    initial_bctxt: BranchCtxt
}

impl FoldUnfold {
    pub fn new(initial_bctxt: BranchCtxt) -> Self {
        FoldUnfold {
            initial_bctxt
        }
    }
}

impl vir::CfgAugmenter<BranchCtxt> for FoldUnfold {
    /// Return the initial branch context
    fn initial_context(&self) -> BranchCtxt {
        self.initial_bctxt.clone()
    }

    /// Prepend some statements to an existing statement, mutating the branch context
    fn prepend_stmt(&self, stmt: &vir::Stmt, bctxt: &mut BranchCtxt) -> Vec<vir::Stmt> {
        bctxt.apply_stmt(stmt)
    }

    /// Prepend some statements to an existing successor, mutating the branch context
    fn prepend_successor(&self, succ: &vir::Successor, bctxt: &mut BranchCtxt) -> Vec<vir::Stmt> {
        bctxt.apply_successor(succ)
    }

    /// Prepend some statements to an existing join point, returning the merged branch context.
    fn prepend_join(&self, bcs: Vec<&BranchCtxt>) -> (Vec<Vec<vir::Stmt>>, BranchCtxt) {
        (
            vec![
                vec![
                    // TODO
                ]
            ],
            bcs[0].clone()
        )
    }

    /// Prepend some statements to a back jump
    fn prepend_back_jump(&self, bc: &BranchCtxt, target_bc: &BranchCtxt) -> Vec<vir::Stmt> {
        assert_eq!(bc.state, target_bc.state);
        vec![]
    }
}
