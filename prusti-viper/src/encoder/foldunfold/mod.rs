// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::vir;
use self::branch_ctxt::*;
use std::collections::HashMap;
use std::collections::HashSet;
use encoder::vir::CfgReplacer;
use encoder::foldunfold::perm::*;
use encoder::foldunfold::permissions::RequiredPermissionsGetter;
use encoder::vir::ExprFolder;
use encoder::vir::ExprIterator;
use prusti_interface::config;

mod perm;
mod permissions;
mod state;
mod branch_ctxt;
mod semantics;
mod places_utils;
mod action;


pub fn add_folding_unfolding(mut function: vir::Function, predicates: HashMap<String, vir::Predicate>) -> vir::Function {
    if function.body.is_none() {
        return function
    }

    let formal_vars = function.formal_args.clone();
    let mut bctxt = BranchCtxt::new(formal_vars, &predicates);
    // Inhale preconditions
    for pre in &function.pres {
        let _ = bctxt.apply_stmt(&vir::Stmt::Inhale(pre.clone()));
    }

    let body = function.body.unwrap();

    let (curr_perms, old_perms) = body
        .get_required_permissions(&predicates)
        .into_iter()
        .group_by_label();

    // Add appropriate unfolding around this expression
    let new_body = bctxt
        .obtain_permissions(curr_perms)
        .into_iter()
        .rev()
        .fold(
            body,
            |expr, action| action.to_expr(expr)
        );

    function.body = Some(new_body);
    function
}


pub fn add_fold_unfold(cfg: vir::CfgMethod, predicates: HashMap<String, vir::Predicate>) -> vir::CfgMethod {
    let cfg_vars = cfg.get_all_vars();
    let initial_bctxt = BranchCtxt::new(cfg_vars, &predicates);
    FoldUnfold::new(initial_bctxt).replace_cfg(&cfg)
}

#[derive(Debug, Clone)]
struct FoldUnfold<'a> {
    initial_bctxt: BranchCtxt<'a>,
    bctxt_at_label: HashMap<String, BranchCtxt<'a>>,
    debug_foldunfold: bool,
}

impl<'a> FoldUnfold<'a> {
    pub fn new(initial_bctxt: BranchCtxt<'a>) -> Self {
        FoldUnfold {
            initial_bctxt,
            bctxt_at_label: HashMap::new(),
            debug_foldunfold: config::debug_foldunfold()
        }
    }

    fn replace_expr(&self, expr: &vir::Expr, curr_bctxt: &BranchCtxt) -> vir::Expr {
        ExprReplacer::new(curr_bctxt, &self.bctxt_at_label).fold(expr.clone())
    }
}

impl<'a> vir::CfgReplacer<BranchCtxt<'a>> for FoldUnfold<'a> {
    /// Give the initial branch context
    fn initial_context(&mut self) -> BranchCtxt<'a> {
        self.initial_bctxt.clone()
    }

    /// Replace some statements, mutating the branch context
    fn replace_stmt(&mut self, stmt: &vir::Stmt, bctxt: &mut BranchCtxt<'a>) -> Vec<vir::Stmt> {
        debug!("replace_stmt: {}", stmt);
        if let vir::Stmt::Label(ref label) = stmt {
            self.bctxt_at_label.insert(label.clone(), bctxt.clone());
        }

        let mut stmts: Vec<vir::Stmt> = vec![];

        // 1. Preferred permissions
        let (preferred_curr_perms, _) = stmt
            .get_preferred_permissions(bctxt.predicates())
            .into_iter()
            .group_by_label();

        let obtainable_preferred_curr_perms: Vec<_> = preferred_curr_perms.into_iter()
            .filter(|p| !bctxt.state().is_prefix_of_some_moved(&p.get_place()))
            .filter(|p| !bctxt.state().moved().iter().any(|mp| p.get_place().has_prefix(mp)))
            .collect();

        if !obtainable_preferred_curr_perms.is_empty() {
            if self.debug_foldunfold {
                stmts.push(vir::Stmt::comment(format!("[foldunfold] Access permissions: {{{}}}", bctxt.state().display_acc())));
                stmts.push(vir::Stmt::comment(format!("[foldunfold] Predicate permissions: {{{}}}", bctxt.state().display_pred())));
            }

            stmts.extend(
                bctxt
                    .obtain_permissions(obtainable_preferred_curr_perms)
                    .iter()
                    .map(|a| a.to_stmt())
            );

            if self.debug_foldunfold {
                stmts.push(vir::Stmt::comment("Assert content of fold/unfold state"));
                stmts.push(vir::Stmt::Assert(bctxt.state().as_vir_expr(), vir::Position::new(0, 0, "check state".to_string())));
            }
        }

        // 2. Required permissions
        let (curr_perms, old_perms) = stmt
            .get_required_permissions(bctxt.predicates())
            .into_iter()
            .group_by_label();

        if !curr_perms.is_empty() {
            if self.debug_foldunfold {
                stmts.push(vir::Stmt::comment(format!("[foldunfold] Access permissions: {{{}}}", bctxt.state().display_acc())));
                stmts.push(vir::Stmt::comment(format!("[foldunfold] Predicate permissions: {{{}}}", bctxt.state().display_pred())));
            }

            stmts.extend(
                bctxt
                    .obtain_permissions(curr_perms)
                    .iter()
                    .map(|a| a.to_stmt())
            );

            if self.debug_foldunfold {
                stmts.push(vir::Stmt::comment("Assert content of fold/unfold state"));
                stmts.push(vir::Stmt::Assert(bctxt.state().as_vir_expr(), vir::Position::new(0, 0, "check state".to_string())));
            }
        }

        // 3. Add "fold/unfolding in" expressions in statement
        let repl_expr = |expr: &vir::Expr| -> vir::Expr {
            self.replace_expr(expr, bctxt)
        };
        let repl_exprs = |exprs: &Vec<vir::Expr>| -> Vec<vir::Expr> {
            exprs.iter().map(|e| self.replace_expr(e, bctxt)).collect()
        };

        let new_stmt= match stmt {
            vir::Stmt::Comment(s) => vir::Stmt::Comment(s.clone()),
            vir::Stmt::Label(s) => vir::Stmt::Label(s.clone()),
            vir::Stmt::Inhale(e) => vir::Stmt::Inhale(repl_expr(e)),
            vir::Stmt::Exhale(e, p) => vir::Stmt::Exhale(repl_expr(e), p.clone()),
            vir::Stmt::Assert(e, p) => vir::Stmt::Assert(repl_expr(e), p.clone()),
            vir::Stmt::MethodCall(s, ve, vv) => vir::Stmt::MethodCall(s.clone(), repl_exprs(ve), vv.clone()),
            vir::Stmt::Assign(p, e, k) => vir::Stmt::Assign(p.clone(), repl_expr(e), k.clone()),
            vir::Stmt::Fold(s, ve, fr) => vir::Stmt::Fold(s.clone(), repl_exprs(ve), *fr),
            vir::Stmt::Unfold(s, ve, fr) => vir::Stmt::Unfold(s.clone(), repl_exprs(ve), *fr),
            vir::Stmt::Obtain(e) => vir::Stmt::Obtain(repl_expr(e)),
            vir::Stmt::WeakObtain(e) => vir::Stmt::WeakObtain(repl_expr(e)),
            vir::Stmt::Havoc => vir::Stmt::Havoc,
            vir::Stmt::BeginFrame => vir::Stmt::BeginFrame,
            vir::Stmt::EndFrame => vir::Stmt::EndFrame,
        };

        // 4. Apply statement
        let _ = bctxt.apply_stmt(&new_stmt);
        stmts.push(new_stmt);

        stmts
    }

    /// Inject some statements and replace a successor, mutating the branch context
    fn replace_successor(&mut self, succ: &vir::Successor, bctxt: &mut BranchCtxt<'a>) -> (Vec<vir::Stmt>, vir::Successor) {
        debug!("replace_successor: {}", succ);
        let exprs: Vec<&vir::Expr> = match succ {
            &vir::Successor::GotoSwitch(ref guarded_targets, _) => {
                guarded_targets.iter().map(|g| &g.0).collect()
            },
            &vir::Successor::GotoIf(ref expr, _, _) => vec![expr],
            _ => vec![]
        };

        let (curr_perms, old_perms) = exprs.iter().flat_map(
            |e| e.get_required_permissions(bctxt.predicates())
        ).group_by_label();

        let mut stmts: Vec<vir::Stmt> = vec![];

        if !curr_perms.is_empty() {
            if self.debug_foldunfold {
                stmts.push(vir::Stmt::comment(format!("[foldunfold] Access permissions: {{{}}}", bctxt.state().display_acc())));
                stmts.push(vir::Stmt::comment(format!("[foldunfold] Predicate permissions: {{{}}}", bctxt.state().display_pred())));
            }

            stmts.extend(
                bctxt
                    .obtain_permissions(curr_perms)
                    .iter()
                    .map(|a| a.to_stmt())
                    .collect::<Vec<_>>()
            );
        }

        if self.debug_foldunfold {
            stmts.push(vir::Stmt::comment("Assert content of fold/unfold state"));
            stmts.push(vir::Stmt::Assert(bctxt.state().as_vir_expr(), vir::Position::new(0, 0, "check state".to_string())));
        }

        // Add "fold/unfolding in" expressions in successor
        let repl_expr = |expr: &vir::Expr| -> vir::Expr {
            self.replace_expr(expr, bctxt)
        };

        let new_succ= match succ {
            vir::Successor::Undefined => vir::Successor::Undefined,
            vir::Successor::Return => vir::Successor::Return,
            vir::Successor::Goto(target) => vir::Successor::Goto(*target),
            vir::Successor::GotoSwitch(guarded_targets, default_target) => {
                vir::Successor::GotoSwitch(
                    guarded_targets
                        .iter()
                        .map(|(cond, targ)| (repl_expr(cond), targ.clone()))
                        .collect::<Vec<_>>(),
                    *default_target
                )
            },
            vir::Successor::GotoIf(condition, then_target, else_target) => {
                vir::Successor::GotoIf(repl_expr(condition), *then_target, *else_target)
            },
        };

        (stmts, new_succ)
    }

    /// Prepend some statements to an existing join point, returning the merged branch context.
    fn prepend_join(&mut self, bcs: Vec<&BranchCtxt<'a>>) -> (Vec<Vec<vir::Stmt>>, BranchCtxt<'a>) {
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
            let (merge_actions_left, merge_actions_right) = left_bc.join(right_bc);
            let merge_bc = left_bc;

            let mut branch_stmts_vec: Vec<Vec<vir::Stmt>> = vec![];
            for left_stmts in left_stmts_vec {
                let mut branch_stmts = left_stmts.clone();
                branch_stmts.extend(merge_actions_left.iter().map(|a| a.to_stmt()).collect::<Vec<_>>());
                branch_stmts_vec.push(branch_stmts);
            }
            for right_stmts in right_stmts_vec {
                let mut branch_stmts = right_stmts.clone();
                branch_stmts.extend(merge_actions_right.iter().map(|a| a.to_stmt()).collect::<Vec<_>>());
                branch_stmts_vec.push(branch_stmts);
            }

            trace!("[exit] prepend_join(..{}): {:?}", &bcs.len(), &branch_stmts_vec);
            (branch_stmts_vec, merge_bc)
        }
    }
}

struct ExprReplacer<'b, 'a: 'b> {
    curr_bctxt: &'b BranchCtxt<'a>,
    bctxt_at_label: &'b HashMap<String, BranchCtxt<'a>>,
}

impl<'b, 'a: 'b> ExprReplacer<'b, 'a>{
    pub fn new(curr_bctxt: &'b BranchCtxt<'a>, bctxt_at_label: &'b HashMap<String, BranchCtxt<'a>>) -> Self {
        ExprReplacer {
            curr_bctxt,
            bctxt_at_label
        }
    }
}

impl<'b, 'a: 'b> ExprFolder for ExprReplacer<'b, 'a> {
    fn fold_labelled_old(&mut self, label: String, expr: Box<vir::Expr>) -> vir::Expr {
        debug!("fold_labelled_old {}: {}", label, expr);

        let mut old_bctxt = self.bctxt_at_label.get(&label).unwrap().clone();

        if label == "pre" {
            // Rename the local variables from `_1, ..` to `_old_1, ..` (see issue #20)
            old_bctxt.mut_state().replace_local_vars(|local_var: &vir::LocalVar| {
                vir::LocalVar::new(
                    format!("_old{}", local_var.name),
                    local_var.typ.clone()
                )
            });
        };

        let (curr_perms, old_perms) = expr
            .get_required_permissions(old_bctxt.predicates())
            .into_iter()
            .group_by_label();

        // Add appropriate unfolding around this old expression
        let inner_expr = old_bctxt
            .obtain_permissions(curr_perms)
            .into_iter()
            .rev()
            .fold(
                *expr,
                |expr, action| action.to_expr(expr)
            );

        vir::Expr::labelled_old(&label, inner_expr)
    }
}
