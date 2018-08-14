// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::vir;
use self::branch_ctxt::*;
use std::collections::HashMap;
use encoder::vir::CfgReplacer;

mod perm;
mod requirements;
mod state;
mod branch_ctxt;
mod semantics;
mod places_utils;

pub fn add_fold_unfold(cfg: vir::CfgMethod, predicates: HashMap<String, vir::Predicate>) -> vir::CfgMethod {
    let cfg_vars = cfg.get_all_vars();
    let initial_bctxt = BranchCtxt::new(cfg_vars, predicates);
    FoldUnfold::new(initial_bctxt).replace_cfg(&cfg)
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

impl vir::CfgReplacer<BranchCtxt> for FoldUnfold {
    /// Give the initial branch context
    fn initial_context(&self) -> BranchCtxt {
        self.initial_bctxt.clone()
    }

    /// Replace some statements, mutating the branch context
    fn replace_stmt(&self, stmt: &vir::Stmt, bctxt: &mut BranchCtxt) -> Vec<vir::Stmt> {
        let mut stmts = bctxt.apply_stmt(stmt);
        stmts.push(stmt.clone());
        stmts
    }

    /// Inject some statements and replace a successor, mutating the branch context
    fn replace_successor(&self, succ: &vir::Successor, bctxt: &mut BranchCtxt) -> (Vec<vir::Stmt>, vir::Successor) {
        (
            bctxt.apply_successor(succ),
            succ.clone()
        )
    }

    /// Prepend some statements to an existing join point, returning the merged branch context.
    fn prepend_join(&self, bcs: Vec<&BranchCtxt>) -> (Vec<Vec<vir::Stmt>>, BranchCtxt) {
        trace!("[enter] prepend_join(..{})", &bcs.len());
        assert!(bcs.len() > 0);
        if bcs.len() == 1 {
            (vec![vec![]], bcs[0].clone())
        } else {
            // Define two subgroups
            let mid = bcs.len() / 2;
            let left_bcs = &bcs[..mid];
            let right_bcs = &bcs[mid..];

            // Join the subgroups
            let (left_stmts_vec, mut left_bc) = self.prepend_join(left_bcs.to_vec());
            let (right_stmts_vec, right_bc) = self.prepend_join(right_bcs.to_vec());

            // Join the recursive calls
            let (merge_stmts_left, merge_stmts_right) = left_bc.join(right_bc);
            let merge_bc = left_bc;

            let mut branch_stmts_vec: Vec<Vec<vir::Stmt>> = vec![];
            for left_stmts in left_stmts_vec {
                let mut branch_stmts = left_stmts.clone();
                branch_stmts.extend(merge_stmts_left.clone());
                branch_stmts_vec.push(branch_stmts);
            }
            for right_stmts in right_stmts_vec {
                let mut branch_stmts = right_stmts.clone();
                branch_stmts.extend(merge_stmts_right.clone());
                branch_stmts_vec.push(branch_stmts);
            }

            trace!("[exit] prepend_join(..{}): {:?}", &bcs.len(), &branch_stmts_vec);
            (branch_stmts_vec, merge_bc)
        }
    }
}
