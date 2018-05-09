// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

mod acc_or_pred;
mod requirements;
mod state;
mod branch_ctxt;
mod semantics;

use std::collections::HashMap;
use encoder::vir;
use self::branch_ctxt::*;

pub fn add_fold_unfold(cfg: vir::CfgMethod, predicates: HashMap<String, vir::Predicate>) -> vir::CfgMethod {
    let cfg_vars = cfg.get_all_vars();
    let initial_bctxt = BranchCtxt::new(cfg_vars, predicates);
    cfg.augment(FoldUnfold::new(initial_bctxt))
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
        assert_eq!(bc, target_bc);
        vec![]
    }
}
