// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

mod required_places;

use encoder::vir;

pub use self::required_places::*;

pub fn add_fold_unfold(cfg: vir::CfgMethod) -> vir::CfgMethod {
    cfg.augment(FoldUnfold::new())
}

#[derive(Debug, Clone)]
struct BranchCtxt {

}

impl BranchCtxt {
    pub fn new() -> Self {
        BranchCtxt {
        }
    }
}

#[derive(Debug, Clone)]
struct FoldUnfold {

}

impl FoldUnfold {
    pub fn new() -> Self {
        FoldUnfold {
        }
    }
}

impl vir::CfgAugmenter<BranchCtxt> for FoldUnfold {
    /// Return the initial branch context
    fn initial_context(&self) -> BranchCtxt {
        BranchCtxt::new()
    }

    /// Prepend some statements to an existing statement, mutating the branch context
    fn prepend_stmt(&self, stmt: &vir::Stmt, bc: &mut BranchCtxt) -> Vec<vir::Stmt> {
        let required_places = stmt.get_required_places();
        if required_places.is_empty() {
            vec![]
        } else {
            vec![
                vir::Stmt::comment(format!(
                    "Required places: {:?}",
                    required_places.iter().map(|x| format!("{}", x)).collect::<Vec<String>>().join(", ")
                ))
            ]
        }
    }

    /// Prepend some statements to an existing successor, mutating the branch context
    fn prepend_successor(&self, succ: &vir::Successor, bc: &mut BranchCtxt) -> Vec<vir::Stmt> {
        vec![
        ]
    }

    /// Prepend some statements to an existing join point, returning the merged branch context.
    fn prepend_join(&self, bcs: Vec<&BranchCtxt>) -> (Vec<Vec<vir::Stmt>>, BranchCtxt) {
        (
            vec![
                vec![
                ]
            ],
            BranchCtxt::new()
        )
    }

    /// Prepend some statements to a back jump
    fn prepend_back_jump(&self, bc: &BranchCtxt, target_bc: &BranchCtxt) -> Vec<vir::Stmt> {
        vec![
        ]
    }
}
