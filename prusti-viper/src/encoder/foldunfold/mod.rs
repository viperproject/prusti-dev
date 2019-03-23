// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::mem;
use encoder::vir;
use encoder::Encoder;
use self::branch_ctxt::*;
use std::collections::HashMap;
use std::collections::HashSet;
use std::cmp::Ordering;
use encoder::vir::{CfgReplacer, CheckNoOpAction, CfgBlockIndex};
use encoder::foldunfold::action::Action;
use encoder::foldunfold::log::EventLog;
use encoder::foldunfold::perm::*;
use encoder::foldunfold::permissions::RequiredPermissionsGetter;
use encoder::vir::ExprFolder;
use encoder::vir::ExprIterator;
use prusti_interface::config;
use prusti_interface::report;
use std;
use encoder::foldunfold::places_utils::*;

mod perm;
mod permissions;
mod state;
mod branch_ctxt;
mod semantics;
mod places_utils;
mod action;
mod log;
mod borrows;

pub fn add_folding_unfolding_to_expr(expr: vir::Expr, bctxt: &BranchCtxt) -> vir::Expr {
    let bctxt_at_label = HashMap::new();
    let expr = ExprReplacer::new(bctxt.clone(), &bctxt_at_label, true).fold(expr);
    ExprReplacer::new(bctxt.clone(), &bctxt_at_label, false).fold(expr)
}

pub fn add_folding_unfolding_to_function(function: vir::Function, predicates: HashMap<String, vir::Predicate>) -> vir::Function {
    // Compute inner state
    let formal_vars = function.formal_args.clone();
    let mut bctxt = BranchCtxt::new(formal_vars, &predicates);
    for pre in &function.pres {
        bctxt.apply_stmt(&vir::Stmt::Inhale(pre.clone()));
    }

    // Add appropriate unfolding around expressions
    vir::Function {
        pres: function.pres.into_iter().map(|e| add_folding_unfolding_to_expr(e, &bctxt)).collect(),
        posts: function.posts.into_iter().map(|e| add_folding_unfolding_to_expr(e, &bctxt)).collect(),
        body: function.body.map(|e| add_folding_unfolding_to_expr(e, &bctxt)),
        ..function
    }
}

pub fn add_fold_unfold<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a>(
    encoder: &'p Encoder<'v, 'r, 'a, 'tcx>,
    cfg: vir::CfgMethod,
    borrow_positions: HashMap<vir::borrows::Borrow, vir::CfgBlockIndex>,
) -> vir::CfgMethod {
    let cfg_vars = cfg.get_all_vars();
    let predicates = encoder.get_used_viper_predicates_map();
    let initial_bctxt = BranchCtxt::new(cfg_vars, &predicates);
    FoldUnfold::new(encoder, initial_bctxt, &cfg, borrow_positions).replace_cfg(&cfg)
}

#[derive(Clone)]
struct FoldUnfold<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> {
    encoder: &'p Encoder<'v, 'r, 'a, 'tcx>,
    initial_bctxt: BranchCtxt<'p>,
    bctxt_at_label: HashMap<String, BranchCtxt<'p>>,
    dump_debug_info: bool,
    check_foldunfold_state: bool,
    cfg: &'p vir::CfgMethod,
    log: EventLog,
    borrow_positions: HashMap<vir::borrows::Borrow, vir::CfgBlockIndex>,
}

impl<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> FoldUnfold<'p, 'v, 'r, 'a, 'tcx> {

    pub fn new(
        encoder: &'p Encoder<'v, 'r, 'a, 'tcx>,
        initial_bctxt: BranchCtxt<'p>,
        cfg: &'p vir::CfgMethod,
        borrow_positions: HashMap<vir::borrows::Borrow, vir::CfgBlockIndex>,
    ) -> Self {
        FoldUnfold {
            encoder,
            initial_bctxt,
            bctxt_at_label: HashMap::new(),
            dump_debug_info: config::dump_debug_info(),
            check_foldunfold_state: config::check_foldunfold_state(),
            cfg,
            log: EventLog::new(),
            borrow_positions,
        }
    }

    fn replace_expr(&self, expr: &vir::Expr, curr_bctxt: &BranchCtxt<'p>) -> vir::Expr {
        ExprReplacer::new(curr_bctxt.clone(), &self.bctxt_at_label, false).fold(expr.clone())
    }

    fn replace_old_expr(&self, expr: &vir::Expr, curr_bctxt: &BranchCtxt<'p>) -> vir::Expr {
        ExprReplacer::new(curr_bctxt.clone(), &self.bctxt_at_label, true).fold(expr.clone())
    }

    /// Insert "unfolding in" in old expressions
    fn rewrite_stmt_with_unfoldings_in_old(&self, stmt: vir::Stmt, bctxt: &BranchCtxt<'p>) -> vir::Stmt {
        trace!("[enter] rewrite_stmt_with_unfoldings_in_old: {}", stmt);
        let result = stmt.map_expr(|e| self.replace_old_expr(&e, bctxt));
        trace!("[exit] rewrite_stmt_with_unfoldings_in_old = {}", result);
        result
    }

    /// Insert "unfolding in" expressions
    fn rewrite_stmt_with_unfoldings(&self, stmt: vir::Stmt, bctxt: &BranchCtxt<'p>) -> vir::Stmt {
        match stmt {
            vir::Stmt::Inhale(expr) => {
                // Compute inner state
                let mut inner_bctxt = bctxt.clone();
                let inner_state = inner_bctxt.mut_state();
                inner_state.insert_all_perms(
                    expr.get_permissions(bctxt.predicates())
                        .into_iter()
                        .filter(|p| !p.get_place().is_local() && p.is_curr())
                );

                // Rewrite statement
                vir::Stmt::Inhale(self.replace_expr(&expr, &inner_bctxt))
            }
            vir::Stmt::TransferPerm(lhs, rhs, unchecked) => {
                // Compute rhs state
                let mut rhs_bctxt = bctxt.clone();
                /*
                let rhs_state = rhs_bctxt.mut_state();
                rhs_state.insert_all_perms(
                    rhs.get_permissions(bctxt.predicates())
                        .into_iter()
                        .filter(|p| p.is_pred())
                );
                */
                let new_lhs = if unchecked {
                    lhs
                } else {
                    self.replace_expr(&lhs, &bctxt)
                };

                // Rewrite statement
                vir::Stmt::TransferPerm(
                    new_lhs,
                    self.replace_old_expr(&rhs, &rhs_bctxt),
                    unchecked
                )
            }
            vir::Stmt::PackageMagicWand(wand, stmts, label, pos) => {
                vir::Stmt::PackageMagicWand(
                    self.replace_expr(&wand, bctxt),
                    stmts,
                    label,
                    pos
                )
            }
            _ => stmt.map_expr(|e| self.replace_expr(&e, bctxt)),
        }
    }

    fn process_expire_borrows(
        &mut self,
        dag: &vir::borrows::DAG,
        surrounding_bctxt: &mut BranchCtxt<'p>,
        surrounding_block_index: vir::CfgBlockIndex,
        new_cfg: &vir::CfgMethod,
        label: Option<&str>,
    ) -> Vec<vir::Stmt> {
        trace!("[enter] process_expire_borrows dag=[{:?}]", dag);
        let mut cfg = borrows::CFG::new();
        for node in dag.iter() {
            trace!("process_expire_borrows construct cfg node={:?}", node);
            let predecessors = node.reborrowing_nodes
                .iter()
                .map(|b| dag.get_borrow_index(*b))
                .collect();
            let successors = node.reborrowed_nodes
                .iter()
                .map(|b| dag.get_borrow_index(*b))
                .collect();
            let block = borrows::BasicBlock {
                node: node,
                guard: dag.guard(node.borrow),
                current_guard: node.guard.clone(),
                predecessors: predecessors,
                statements: vec![vir::Stmt::comment(format!("{:?}", node.borrow))],
                successors: successors,
            };
            cfg.add_block(block);
        }

        let mut initial_bctxt: Vec<Option<BranchCtxt>> = vec![None; cfg.basic_blocks.len()];
        let mut final_bctxt: Vec<Option<BranchCtxt>> = vec![None; cfg.basic_blocks.len()];

        for curr_block_index in 0..cfg.basic_blocks.len() {

            if self.dump_debug_info {
                let source_path = self.encoder.env().source_path();
                let source_filename = source_path.file_name().unwrap().to_str().unwrap();
                report::log::report_with_writer(
                    "graphviz_reborrowing_dag_during_foldunfold",
                    format!("{}.{}.dot", source_filename, dag),
                    |writer| cfg.to_graphviz(writer, curr_block_index)
                );
            }

            let mut curr_block_pre_statements = Vec::new();

            let curr_block = &cfg.basic_blocks[curr_block_index];
            let curr_node = &curr_block.node;
            let mut bctxt = if curr_block.predecessors.is_empty() {
                let mut bctxt = surrounding_bctxt.clone();
                let end_block = surrounding_block_index;
                let start_block = self.borrow_positions[&curr_node.borrow];
                if !start_block.weak_eq(&end_block) {
                    let path = new_cfg.find_path(start_block, end_block);
                    debug!("process_expire_borrows borrow={:?} path={:?}",
                           curr_node.borrow, path);
                    let dropped_permissions = self.log.collect_dropped_permissions(&path, dag);
                    debug!("process_expire_borrows borrow={:?} dropped_permissions={:?}",
                           curr_node.borrow, dropped_permissions);
                    for perm in &dropped_permissions {
                        let comment = format!("restored: {}", perm);
                        curr_block_pre_statements.push(vir::Stmt::comment(comment));
                    }
                    bctxt.mut_state().restore_dropped_perms(dropped_permissions.into_iter());
                    bctxt
                } else {
                    bctxt
                }
            } else {
                let mut incoming_bctxt = Vec::new();
                for &predecessor in &curr_block.predecessors {
                    let mut bctxt = final_bctxt[predecessor].as_ref().unwrap().clone();
                    let predecessor_node = &cfg.basic_blocks[predecessor].node;
                    let end_block = self.borrow_positions[&predecessor_node.borrow];
                    let start_block = self.borrow_positions[&curr_node.borrow];
                    if start_block != end_block {
                        let path = new_cfg.find_path(start_block, end_block);
                        debug!("process_expire_borrows borrow={:?} path={:?}",
                               curr_node.borrow, path);
                        let dropped_permissions = self.log.collect_dropped_permissions(&path, dag);
                        debug!("process_expire_borrows borrow={:?} dropped_permissions={:?}",
                               curr_node.borrow, dropped_permissions);
                        for perm in &dropped_permissions {
                            let comment = format!("restored: {}", perm);
                            let key = (predecessor, curr_block_index);
                            let entry = cfg.edges.entry(key).or_insert(Vec::new());
                            entry.push(vir::Stmt::comment(comment));
                        }
                        bctxt.mut_state().restore_dropped_perms(dropped_permissions.into_iter());
                    }
                    incoming_bctxt.push(bctxt);
                }
                let incoming_bctxt_refs = incoming_bctxt.iter().collect();
                let (actions, mut bctxt) = self.prepend_join(incoming_bctxt_refs);
                for (&src_index, mut action) in curr_block.predecessors.iter().zip(&actions) {
                    assert!(src_index < curr_block_index);
                    if !action.is_empty() {
                        //let stmts_to_add = action.iter().map(|a| a.to_stmt()).collect();
                        let mut stmts_to_add = Vec::new();
                        for a in action {
                            stmts_to_add.push(a.to_stmt());
                            if let Action::Drop(perm) = a {
                                if dag.in_borrowed_places(perm.get_place()) {
                                    stmts_to_add.push(vir::Stmt::comment(format!("restored: {}", perm)));
                                    bctxt.mut_state().restore_dropped_perm(perm.clone());
                                }
                            }
                        }
                        let key = (src_index, curr_block_index);
                        let entry = cfg.edges.entry(key).or_insert(Vec::new());
                        entry.extend(stmts_to_add);
                    }
                }
                bctxt
            };
            initial_bctxt[curr_block_index] = Some(bctxt.clone());

            let curr_block = &mut cfg.basic_blocks[curr_block_index];
            let curr_node = &curr_block.node;
            curr_block.statements.extend(curr_block_pre_statements);

            for stmt in &curr_node.stmts {
                debug!("process_expire_borrows block={} ({:?}) stmt={}",
                       curr_block_index, curr_node.borrow, stmt);
                let new_stmts = self.replace_stmt(
                    &stmt, false, &mut bctxt, surrounding_block_index, new_cfg, label);
                curr_block.statements.extend(new_stmts);
            }

            // Remove read permissions.
            let duplicated_perms = self.log.get_duplicated_read_permissions(curr_node.borrow);
            let mut maybe_original_place = None;
            for (mut read_access, original_place) in duplicated_perms {
                if let Some(ref place) = curr_node.place {
                    debug!("place={} original_place={} read_access={}",
                           place, original_place, read_access);
                    read_access = read_access.replace_place(&original_place, place);
                }
                maybe_original_place = Some(original_place);
                let stmt = vir::Stmt::Exhale(read_access, vir::Position::default());
                let new_stmts = self.replace_stmt(
                    &stmt, false, &mut bctxt, surrounding_block_index, new_cfg, label);
                curr_block.statements.extend(new_stmts);
            }
            if let Some(original_place) = maybe_original_place {
                if bctxt.state().contains_acc(&original_place) {
                    bctxt.mut_state().insert_moved(original_place);
                }
            }
            // Restore write permissions.
            // Currently, we have a simplified version that restores write permissions only when
            // all borrows in the conflict set are dead. This is sound, but less complete.
            // TODO: Implement properly so that we can restore write permissions to the prefix only
            // when there is still alive conflicting borrown. For example, when the currently expiring
            // borrow borrowed `x.f`, but we still have a conflicting borrow that borrowed `x.f.g`, we
            // would need to restore write permissions to `x.f` without doing the same for `x.f.g`.
            // This would require making sure that we are unfolded up to `x.f.g` and emit
            // restoration for each place segment separately.
            if curr_node.alive_conflicting_borrows.is_empty() {
                for &borrow in &curr_node.conflicting_borrows {
                    curr_block.statements.extend(
                        self.restore_write_permissions(borrow, &mut bctxt));
                }
                curr_block.statements.extend(
                    self.restore_write_permissions(curr_node.borrow, &mut bctxt));
            }

            final_bctxt[curr_block_index] = Some(bctxt);
        }

        // Merge all bctxts with reborrowed_nodes.is_empty() into one.
        let final_blocks: Vec<_> = cfg.basic_blocks
            .iter()
            .enumerate()
            .filter(|(_, block)| block.successors.is_empty())
            .map(|(i, _)| i)
            .collect();
        let final_bctxts: Vec<_> = final_blocks
            .iter()
            .map(|i| final_bctxt[*i].as_ref().unwrap())
            .collect();
        let (actions, mut final_bctxt) = self.prepend_join(final_bctxts);
        for (&i, mut action) in final_blocks.iter().zip(actions.iter()) {
            if !action.is_empty() {
                let mut stmts_to_add = Vec::new();
                for a in action {
                    stmts_to_add.push(a.to_stmt());
                    if let Action::Drop(perm) = a {
                        if dag.in_borrowed_places(perm.get_place()) {
                            stmts_to_add.push(vir::Stmt::comment(format!("restored: {}", perm)));
                            final_bctxt.mut_state().restore_dropped_perm(perm.clone());
                        }
                    }
                }
                //let stmts_to_add = action.iter().map(|a| a.to_stmt());
                cfg.basic_blocks[i].statements.extend(stmts_to_add);
            }
        }
        mem::swap(surrounding_bctxt, &mut final_bctxt);

        let mut stmts = Vec::new();
        for (i, block) in cfg.basic_blocks.iter().enumerate() {
            stmts.push(vir::Stmt::If(block.guard.clone(),
                                     self.patch_places(&block.statements, label)));
            for ((from, to), statements) in &cfg.edges {
                if *from == i {
                    let condition = vir::Expr::and(
                        block.guard.clone(),
                        cfg.basic_blocks[*to].current_guard.clone(),
                    );
                    stmts.push(vir::Stmt::If(condition,
                                             self.patch_places(statements, label)));
                }
            }
        }
        stmts
    }

    /// Restore `Write` permissions that were converted to `Read` due to borrowing.
    fn restore_write_permissions(
        &self,
        borrow: vir::borrows::Borrow,
        bctxt: &mut BranchCtxt
    ) -> Vec<vir::Stmt> {
        let mut stmts = Vec::new();
        for access in self.log.get_converted_to_read_places(borrow) {
            let perm = match access {
                vir::Expr::PredicateAccessPredicate(_, ref args, perm_amount, _) => {
                    assert!(args.len() == 1);
                    Perm::pred(args[0].clone(), perm_amount)
                },
                vir::Expr::FieldAccessPredicate(box ref place, perm_amount, _) => {
                    Perm::acc(place.clone(), perm_amount)
                },
                x => unreachable!("{:?}", x),
            };
            stmts.extend(
                bctxt
                    .obtain_permissions(vec![perm])
                    .iter()
                    .map(|a| a.to_stmt())
            );
            let inhale_stmt = vir::Stmt::Inhale(access);
            bctxt.apply_stmt(&inhale_stmt);
            stmts.push(inhale_stmt);
        }
        stmts
    }

    /// Wrap `_1.val_ref.f.g.` into `old[label](_1.val_ref).f.g`. This is needed
    /// to make `_1.val_ref` reachable inside a package statement of a magic wand.
    fn patch_places(&self, stmts: &Vec<vir::Stmt>, maybe_label: Option<&str>) -> Vec<vir::Stmt> {
        if let Some(label) = maybe_label {
            struct PlacePatcher<'a> {
                label: &'a str,
            }
            impl<'a> vir::ExprFolder for PlacePatcher<'a> {
                fn fold(&mut self, e: vir::Expr) -> vir::Expr {
                    match e {
                        vir::Expr::Field(box vir::Expr::Local(_, _), _, _) => {
                            e.old(self.label)
                        }
                        _ => {
                            vir::default_fold_expr(self, e)
                        }
                    }
                }
            }
            fn patch_args(label: &str, args: &Vec<vir::Expr>) -> Vec<vir::Expr> {
                args.iter()
                    .cloned()
                    .map(|arg| {
                        assert!(arg.is_place());
                        if arg.is_old() {
                            arg
                        } else {
                            PlacePatcher { label }.fold(arg)
                        }
                    })
                    .collect()
            }
            stmts
                .iter()
                .map(|stmt| {
                    match stmt {
                        vir::Stmt::Comment(_) |
                        vir::Stmt::ApplyMagicWand(_, _) |
                        vir::Stmt::TransferPerm(_, _, _) => {
                            stmt.clone()
                        },
                        vir::Stmt::Fold(ref pred_name, ref args, perm_amount) => {
                            vir::Stmt::Fold(pred_name.clone(), patch_args(label, args), *perm_amount)
                        },
                        vir::Stmt::Unfold(ref pred_name, ref args, perm_amount) => {
                            vir::Stmt::Unfold(pred_name.clone(), patch_args(label, args), *perm_amount)
                        },
                        x => unreachable!("{:?}", x),
                    }
                })
                .collect()
        } else {
            stmts.clone()
        }
    }
}

impl CheckNoOpAction for Vec<Action> {
    fn is_noop(&self) -> bool {
        self.is_empty()
    }
}

impl<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> vir::CfgReplacer<BranchCtxt<'p>, Vec<Action>>
        for FoldUnfold<'p, 'v, 'r, 'a, 'tcx> {
    /// Dump the current CFG, for debugging purposes
    fn current_cfg(&self, new_cfg: &vir::CfgMethod) {
        if self.dump_debug_info {
            let source_path = self.encoder.env().source_path();
            let source_filename = source_path.file_name().unwrap().to_str().unwrap();
            let method_name = new_cfg.name();
            report::log::report_with_writer(
                "graphviz_method_during_foldunfold",
                format!("{}.{}.dot", source_filename, method_name),
                |writer| new_cfg.to_graphviz(writer)
            );
        }
    }

    fn check_compatible_back_edge(left: &BranchCtxt<'p>, right: &BranchCtxt<'p>) {
        let left_state = left.state();
        let right_state = right.state();

        // TODO: re-enable this consistency check, discarding all places for which `.is_simple_place()` is false
        //debug_assert_eq!(left_state.acc(), right_state.acc(), "back edge (acc)");
        //debug_assert_eq!(left_state.pred(), right_state.pred(), "back edge (pred)");
        //debug_assert_eq!(left_state.framing_stack(), right_state.framing_stack(), "back edge (framing)");
    }

    /// Give the initial branch context
    fn initial_context(&mut self) -> BranchCtxt<'p> {
        self.initial_bctxt.clone()
    }

    /// Replace some statements, mutating the branch context
    fn replace_stmt(
        &mut self,
        stmt: &vir::Stmt,
        is_last_before_return: bool,
        bctxt: &mut BranchCtxt<'p>,
        curr_block_index: vir::CfgBlockIndex,
        new_cfg: &vir::CfgMethod,
        label: Option<&str>,
    ) -> Vec<vir::Stmt> {
        debug!("[enter] replace_stmt: ##### {} #####", stmt);

        if let vir::Stmt::ExpireBorrows(ref dag) = stmt {
            return self.process_expire_borrows(dag, bctxt, curr_block_index, new_cfg, label);
        }

        let mut stmt = stmt.clone();

        // Store state for old expressions
        match stmt {
            vir::Stmt::Label(ref label) => {
                let mut labelled_bctxt = bctxt.clone();
                let labelled_state = labelled_bctxt.mut_state();
                labelled_state.replace_places(|place| place.old(label));
                self.bctxt_at_label.insert(label.to_string(), labelled_bctxt);
            }

            vir::Stmt::PackageMagicWand(vir::Expr::MagicWand(box ref lhs, _, _), ..) |
            vir::Stmt::ApplyMagicWand(vir::Expr::MagicWand(box ref lhs, _, _), ..) => {
                // TODO: This should be done also for magic wand expressions inside inhale/exhale.
                let label = "lhs".to_string();
                let mut labelled_bctxt = bctxt.clone();
                let labelled_state = labelled_bctxt.mut_state();
                labelled_state.remove_all();
                vir::Stmt::Inhale(lhs.clone()).apply_on_state(labelled_state, bctxt.predicates());
                if let vir::Expr::PredicateAccessPredicate(ref name, ref args, perm_amount, _) = lhs {
                    labelled_state.insert_acc(args[0].clone(), *perm_amount);
                }
                labelled_state.replace_places(|place| place.old(&label));
                self.bctxt_at_label.insert(label.to_string(), labelled_bctxt);
            }

            _ => {} // Nothing
        }

        let mut stmts: Vec<vir::Stmt> = vec![];

        // 0. Insert "unfolding in" inside old expressions. This handles *old* requirements.
        debug!("[step.0] replace_stmt: {}", stmt);
        stmt = self.rewrite_stmt_with_unfoldings_in_old(stmt, &bctxt);

        // 1. Obtain "preferred" permissions (i.e. due to "weak obtain" statements)
        debug!("[step.1] replace_stmt: {}", stmt);
        let preferred_perms: Vec<_> = stmt
            .get_preferred_permissions(bctxt.predicates())
            .into_iter()
            .filter(|p| p.is_curr())
            .collect();

        let obtainable_preferred_perms: Vec<_> = preferred_perms.into_iter()
            .filter(|p| !(p.is_curr() && bctxt.state().is_prefix_of_some_moved(&p.get_place())))
            .filter(|p| !(p.is_curr() && bctxt.state().moved().iter().any(|mp| p.get_place().has_prefix(mp))))
            .collect();

        if !obtainable_preferred_perms.is_empty() {
            stmts.extend(
                bctxt
                    .obtain_permissions(obtainable_preferred_perms)
                    .iter()
                    .map(|a| a.to_stmt())
            );

            if self.check_foldunfold_state {
                stmts.push(vir::Stmt::comment("Assert content of fold/unfold state"));
                stmts.push(vir::Stmt::Assert(bctxt.state().as_vir_expr(), vir::Position::new(0, 0, "check fold/unfold state".to_string())));
            }
        }

        // 2. Obtain required *curr* permissions. *old* requirements will be handled at steps 0 and/or 4.
        debug!("[step.2] replace_stmt: {}", stmt);
        let all_perms = stmt.get_required_permissions(bctxt.predicates());
        let pred_permissions: Vec<_> = all_perms.iter().cloned().filter(|p| p.is_pred()).collect();
        let acc_permissions: Vec<_> = all_perms
            .into_iter()
            .filter(|p| {
                if !p.is_acc() {
                    false
                } else {
                    if p.is_curr() {
                        true
                    } else {
                        pred_permissions
                            .iter()
                            .any(|pred_p| pred_p.get_place() == p.get_place())
                    }
                }
            })
            .collect();

        let mut perms = acc_permissions;
        perms.extend(pred_permissions.into_iter());
        debug!("required permissions: {{\n{}\n}}", perms.iter().map(|x| format!("  {:?}", x)).collect::<Vec<_>>().join(",\n"));

        if !perms.is_empty() {
            stmts.extend(
                bctxt
                    .obtain_permissions(perms)
                    .iter()
                    .map(|a| a.to_stmt())
            );

            if self.check_foldunfold_state && !is_last_before_return {
                stmts.push(vir::Stmt::comment("Assert content of fold/unfold state"));
                stmts.push(vir::Stmt::Assert(bctxt.state().as_vir_expr(), vir::Position::new(0, 0, "check fold/unfold state".to_string())));
            }
        }

        // 3. Replace special statements
        debug!("[step.3] replace_stmt: {}", stmt);
        stmt = match stmt {
            vir::Stmt::PackageMagicWand(
                vir::Expr::MagicWand(box ref lhs, box ref rhs, _),
                ref old_package_stmts,
                ref label,
                ref position
            ) => {
                let mut package_bctxt = bctxt.clone();
                let mut package_stmts = vec![];
                for stmt in old_package_stmts {
                    package_stmts.extend(
                        self.replace_stmt(stmt, false, &mut package_bctxt,
                                          curr_block_index, new_cfg, Some(label))
                    );
                    if config::dump_debug_info() {
                        //package_stmts.push(
                        //    vir::Stmt::comment(format!("[state] acc: {{\n{}\n}}", package_bctxt.state().display_acc()))
                        //);
                        //package_stmts.push(
                        //    vir::Stmt::comment(format!("[state] pred: {{\n{}\n}}", package_bctxt.state().display_pred()))
                        //);
                        report::log::report(
                            "vir_package",
                            "package.vir",
                            vir::Stmt::package_magic_wand(
                                lhs.clone(),
                                rhs.clone(),
                                package_stmts.clone(),
                                label.clone(),
                                position.clone()
                            )
                        );
                    }
                }
                vir::Stmt::package_magic_wand(lhs.clone(), rhs.clone(), package_stmts,
                                              label.clone(), position.clone())
            }
            stmt => stmt,
        };

        // 4. Add "unfolding" expressions in statement. This handles *old* requirements.
        debug!("[step.4] replace_stmt: Add unfoldings in stmt {}", stmt);
        stmt = self.rewrite_stmt_with_unfoldings(stmt, &bctxt);

        // 5. Apply effect of statement on state
        debug!("[step.5] replace_stmt: {}", stmt);
        bctxt.apply_stmt(&stmt);
        stmts.push(stmt.clone());

        // 6. Handle shared borrows.
        debug!("[step.6] replace_stmt: {}", stmt);
        if let vir::Stmt::Assign(
                ref lhs_place,
                ref rhs_place,
                vir::AssignKind::SharedBorrow(borrow)
        ) = stmt {
            // Check if in the state we have any write permissions
            // with the borrowed place as a prefix. If yes, change them
            // to read permissions and emit exhale acc(T(place), write-read).
            let mut acc_perm_counter = 0;
            let mut acc_perms: Vec<_> = bctxt.state().acc().iter()
                .filter(|&(place, perm_amount)| {
                    assert!(perm_amount.is_valid_for_specs());
                    place.has_prefix(rhs_place) &&
                    !place.is_local()
                })
                .map(|(place, perm_amount)| {
                    acc_perm_counter += 1;
                    (place.clone(), perm_amount.clone(), acc_perm_counter)
                })
                .collect();
            acc_perms.sort_by(
                |(place1, _, id1), (place2, _, id2)| {
                    let key1 = (place1.place_depth(), id1);
                    let key2 = (place2.place_depth(), id2);
                    key1.cmp(&key2)
                });
            trace!("acc_perms = {}",
                   acc_perms.iter()
                        .map(|(a, p, id)| format!("({}, {}, {}), ", a, p, id))
                        .collect::<String>());
            for (place, perm_amount, _) in acc_perms {
                debug!("acc place: {} {}", place, perm_amount);
                debug!("rhs_place={} {:?}", rhs_place, bctxt.state().acc().get(rhs_place));
                debug!("lhs_place={} {:?}", lhs_place, bctxt.state().acc().get(lhs_place));
                if *rhs_place == place {
                    if Some(&vir::PermAmount::Write) == bctxt.state().acc().get(lhs_place) {
                        // We are copying a shared reference, so we do not need to change
                        // the root of rhs.
                        debug!("Copy of a shared reference. Ignore.");
                        continue;
                    }
                }
                if perm_amount == vir::PermAmount::Write {
                    let access = vir::Expr::FieldAccessPredicate(
                        box place.clone(), vir::PermAmount::Remaining, vir::Position::default());
                    self.log.log_convertion_to_read(borrow, access.clone());
                    let stmt = vir::Stmt::Exhale(access, vir::Position::default());
                    bctxt.apply_stmt(&stmt);
                    stmts.push(stmt);
                }
                let new_place = place.replace_place(rhs_place, lhs_place);
                debug!("    new place: {}", new_place);
                let lhs_read_access = vir::Expr::FieldAccessPredicate(
                    box new_place, vir::PermAmount::Read, vir::Position::default());
                self.log.log_read_permission_duplication(
                    borrow, lhs_read_access.clone(), lhs_place.clone());
                let stmt = vir::Stmt::Inhale(lhs_read_access);
                bctxt.apply_stmt(&stmt);
                stmts.push(stmt);
            }
            let pred_perms: Vec<_> = bctxt.state().pred().iter()
                .filter(|&(place, perm_amount)| {
                    assert!(perm_amount.is_valid_for_specs());
                    place.has_prefix(rhs_place)
                })
                .map(|(place, perm_amount)| (place.clone(), perm_amount.clone()))
                .collect();
            for (place, perm_amount) in pred_perms {
                debug!("pred place: {} {}", place, perm_amount);
                let predicate_name = place.typed_ref_name().unwrap();
                if perm_amount == vir::PermAmount::Write {
                    let access = vir::Expr::PredicateAccessPredicate(
                        predicate_name.clone(), vec![place.clone()],
                        vir::PermAmount::Remaining, vir::Position::default());
                    self.log.log_convertion_to_read(borrow, access.clone());
                    let stmt = vir::Stmt::Exhale(access, vir::Position::default());
                    bctxt.apply_stmt(&stmt);
                    stmts.push(stmt);
                }
                let new_place = place.replace_place(rhs_place, lhs_place);
                debug!("    new place: {}", new_place);
                let lhs_read_access = vir::Expr::PredicateAccessPredicate(
                    predicate_name, vec![new_place],
                    vir::PermAmount::Read, vir::Position::default());
                self.log.log_read_permission_duplication(
                    borrow, lhs_read_access.clone(), lhs_place.clone());
                let stmt = vir::Stmt::Inhale(lhs_read_access);
                bctxt.apply_stmt(&stmt);
                stmts.push(stmt);
            }
        }

        // Delete lhs state
        self.bctxt_at_label.remove("lhs");

        debug!(
            "[exit] replace_stmt = [\n{}\n]",
            stmts.iter().map(|s| s.to_string()).collect::<Vec<_>>().join("\n  ")
        );
        stmts
    }

    /// Inject some statements and replace a successor, mutating the branch context
    fn replace_successor(&mut self, succ: &vir::Successor, bctxt: &mut BranchCtxt<'p>) -> (Vec<vir::Stmt>, vir::Successor) {
        debug!("replace_successor: {}", succ);
        let exprs: Vec<&vir::Expr> = match succ {
            &vir::Successor::GotoSwitch(ref guarded_targets, _) => {
                guarded_targets.iter().map(|g| &g.0).collect()
            },
            &vir::Successor::GotoIf(ref expr, _, _) => vec![expr],
            _ => vec![]
        };

        let grouped_perms: HashMap<_, _> = exprs.iter().flat_map(
            |e| e.get_required_permissions(bctxt.predicates())
        ).group_by_label();

        let mut stmts: Vec<vir::Stmt> = vec![];

        let mut some_perms_required = false;
        for (label, perms) in grouped_perms.into_iter() {
            debug!("Obtain at label {:?} permissions {:?}", label, perms);
            // Hack: skip old permissions
            if label.is_some() {
                continue;
            }
            if !perms.is_empty() {
                some_perms_required = true;
                let mut opt_old_bctxt = label.map(
                    |label_name| self.bctxt_at_label.get(&label_name).unwrap().clone()
                );
                let label_bctxt = opt_old_bctxt.as_mut().unwrap_or(bctxt);
                stmts.extend(
                    label_bctxt
                        .obtain_permissions(perms)
                        .iter()
                        .map(|a| a.to_stmt())
                        .collect::<Vec<_>>()
                );
            }
        }

        if some_perms_required && self.check_foldunfold_state {
            stmts.push(vir::Stmt::comment("Assert content of fold/unfold state"));
            stmts.push(vir::Stmt::Assert(bctxt.state().as_vir_expr(), vir::Position::new(0, 0, "check fold/unfold state".to_string())));
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

    /// Compute actions that need to be performed before the join point,
    /// returning the merged branch context.
    fn prepend_join(&mut self, bcs: Vec<&BranchCtxt<'p>>) -> (Vec<Vec<Action>>, BranchCtxt<'p>) {
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
            let (left_actions_vec, mut left_bc) = self.prepend_join(left_bcs.to_vec());
            let (right_actions_vec, right_bc) = self.prepend_join(right_bcs.to_vec());

            // Join the recursive calls
            let (merge_actions_left, merge_actions_right) = left_bc.join(right_bc);
            let merge_bc = left_bc;

            let mut branch_actions_vec: Vec<Vec<Action>> = vec![];
            for mut left_actions in left_actions_vec {
                left_actions.extend(merge_actions_left.iter().cloned());
                branch_actions_vec.push(left_actions);
            }
            for mut right_actions in right_actions_vec {
                right_actions.extend(merge_actions_right.iter().cloned());
                branch_actions_vec.push(right_actions);
            }

            trace!("[exit] prepend_join(..{}): {:?}", &bcs.len(), &branch_actions_vec);
            (branch_actions_vec, merge_bc)
        }
    }

    /// Convert actions to statements and log them.
    fn perform_prejoin_action(
        &mut self,
        block_index: CfgBlockIndex,
        actions: Vec<Action>
    ) -> Vec<vir::Stmt> {
        let mut stmts = Vec::new();
        for action in actions {
            stmts.push(action.to_stmt());
            self.log.log_prejoin_action(block_index, action);
        }
        stmts
    }
}

struct ExprReplacer<'b, 'a: 'b> {
    curr_bctxt: BranchCtxt<'a>,
    bctxt_at_label: &'b HashMap<String, BranchCtxt<'a>>,
    lhs_bctxt: Option<BranchCtxt<'a>>,
    wait_old_expr: bool,
}

impl<'b, 'a: 'b> ExprReplacer<'b, 'a>{
    pub fn new(curr_bctxt: BranchCtxt<'a>, bctxt_at_label: &'b HashMap<String, BranchCtxt<'a>>, wait_old_expr: bool) -> Self {
        ExprReplacer {
            curr_bctxt,
            bctxt_at_label,
            lhs_bctxt: None,
            wait_old_expr
        }
    }
}

impl<'b, 'a: 'b> ExprFolder for ExprReplacer<'b, 'a> {
    fn fold_field(&mut self, expr: Box<vir::Expr>, field: vir::Field, pos: vir::Position) -> vir::Expr {
        debug!("[enter] fold_field {}, {}", expr, field);

        let res = if self.wait_old_expr {
            vir::Expr::Field(self.fold_boxed(expr), field, pos)
        } else {
            // FIXME: we lose positions
            let (base, mut fields) = expr.explode_place();
            fields.push(field);
            let new_base = self.fold(base);
            debug_assert!(match new_base {
                vir::Expr::Local(..) |
                vir::Expr::LabelledOld(..) => true,
                _ => false
            });
            fields.into_iter()
                .fold(
                    new_base,
                    |res, f| res.field(f).set_pos(pos.clone())
                )
        };

        debug!("[exit] fold_unfolding = {}", res);
        res
    }

    fn fold_unfolding(
        &mut self,
        name: String,
        args: Vec<vir::Expr>,
        expr: Box<vir::Expr>,
        perm: vir::PermAmount,
        pos: vir::Position
    ) -> vir::Expr {
        debug!("[enter] fold_unfolding {}, {}, {}, {}", name, args[0], expr, perm);

        let res = if self.wait_old_expr {
            vir::Expr::Unfolding(name, args, self.fold_boxed(expr), perm, pos)
        } else {
            // Compute inner state
            let mut inner_bctxt = self.curr_bctxt.clone();
            let inner_state = inner_bctxt.mut_state();
            vir::Stmt::Unfold(name.clone(), args.clone(), perm).apply_on_state(inner_state, self.curr_bctxt.predicates());

            // Store states
            let mut tmp_curr_bctxt = inner_bctxt;
            std::mem::swap(&mut self.curr_bctxt, &mut tmp_curr_bctxt);

            let inner_expr = self.fold_boxed(expr);

            // Restore states
            std::mem::swap(&mut self.curr_bctxt, &mut tmp_curr_bctxt);

            vir::Expr::Unfolding(name, args, inner_expr, perm, pos)
        };

        debug!("[exit] fold_unfolding = {}", res);
        res
    }

    fn fold_magic_wand(&mut self, lhs: Box<vir::Expr>, rhs: Box<vir::Expr>, pos: vir::Position) -> vir::Expr {
        debug!("[enter] fold_magic_wand {}, {}", lhs, rhs);

        // Compute lhs state
        let mut lhs_bctxt = self.curr_bctxt.clone();
        let lhs_state = lhs_bctxt.mut_state();
        lhs_state.remove_all();
        lhs_state.insert_all_perms(
            lhs.get_permissions(self.curr_bctxt.predicates())
                .into_iter()
                .filter(|p| p.is_pred())
                .flat_map(|p| vec![Perm::acc(p.get_place().clone(), p.get_perm_amount()), p])
        );
        lhs_state.replace_places(|place| {
            let pos = place.pos().clone();
            place.old("lhs").set_pos(pos)
        });
        debug!("State of lhs of magic wand: {}", lhs_state);

        // Store states
        std::mem::swap(&mut self.curr_bctxt, &mut lhs_bctxt);

        // Rewrite lhs
        let new_lhs = self.fold_boxed(lhs);

        // Restore states
        std::mem::swap(&mut self.curr_bctxt, &mut lhs_bctxt);

        // Computer lhs state, now with unfoldings
        let mut new_lhs_bctxt = self.curr_bctxt.clone();
        let new_lhs_state = new_lhs_bctxt.mut_state();
        new_lhs_state.remove_all();
        new_lhs_state.insert_all_perms(
            new_lhs.get_permissions(self.curr_bctxt.predicates())
                .into_iter()
                .filter(|p| p.is_pred())
                .flat_map(|p| vec![Perm::acc(p.get_place().clone(), p.get_perm_amount()), p])
        );
        new_lhs_state.replace_places(|place| {
            let pos = place.pos().clone();
            place.old("lhs").set_pos(pos)
        });
        debug!("New state of lhs of magic wand: {}", new_lhs_state);

        // Compute rhs state
        let mut rhs_bctxt = self.curr_bctxt.clone();
        let rhs_state = rhs_bctxt.mut_state();
        rhs_state.remove_all();
        rhs_state.insert_all_perms(
            rhs.get_permissions(self.curr_bctxt.predicates())
                .into_iter()
                .filter(|p| p.is_pred())
                .flat_map(|p| vec![Perm::acc(p.get_place().clone(), p.get_perm_amount()), p])
        );
        debug!("State of rhs of magic wand: {}", rhs_state);

        // Store states
        std::mem::swap(&mut self.curr_bctxt, &mut rhs_bctxt);
        self.lhs_bctxt = Some(new_lhs_bctxt);

        // Rewrite rhs
        let new_rhs = self.fold_boxed(rhs);

        // Restore states
        self.lhs_bctxt = None;
        std::mem::swap(&mut self.curr_bctxt, &mut rhs_bctxt);

        // Rewrite lhs and build magic wand
        let res = vir::Expr::MagicWand(new_lhs, new_rhs, pos);

        debug!("[enter] fold_magic_wand = {}", res);
        res
    }

    fn fold_labelled_old(&mut self, label: String, expr: Box<vir::Expr>, pos: vir::Position) -> vir::Expr {
        debug!("[enter] fold_labelled_old {}: {}", label, expr);

        let mut tmp_curr_bctxt = if label == "lhs" && self.lhs_bctxt.is_some() {
            self.lhs_bctxt.as_ref().unwrap().clone()
        } else {
            self.bctxt_at_label.get(&label).unwrap().clone()
        };

        // Replace old[label] with curr
        tmp_curr_bctxt.mut_state().replace_places(
            |place| place.map_labels(
                |opt_label| {
                    if opt_label == label.clone() {
                        None
                    } else {
                        Some(opt_label)
                    }
                }
            )
        );

        // Store states
        std::mem::swap(&mut self.curr_bctxt, &mut tmp_curr_bctxt);
        let old_wait_old_expr = self.wait_old_expr;
        self.wait_old_expr = false;

        // Rewrite inner expression
        let inner_expr = self.fold_boxed(expr);

        // Restore states
        std::mem::swap(&mut self.curr_bctxt, &mut tmp_curr_bctxt);
        self.wait_old_expr = old_wait_old_expr;

        // Rebuild expression
        let res = vir::Expr::LabelledOld(label, inner_expr, pos);

        debug!("[exit] fold_labelled_old = {}", res);
        res
    }

    fn fold(&mut self, expr: vir::Expr) -> vir::Expr {
        debug!("[enter] fold {}", expr);

        let res = if self.wait_old_expr || !expr.is_pure() {
            vir::default_fold_expr(self, expr)
        } else {
            // Try to add unfolding
            let inner_expr = vir::default_fold_expr(self, expr);
            let perms: Vec<_> = inner_expr
                .get_required_permissions(self.curr_bctxt.predicates())
                .into_iter()
                .filter(|p| p.is_curr())
                .collect();

            debug!(
                "get_required_permissions for {}: {{\n  {}\n}}",
                inner_expr,
                perms.iter().map(|p| p.to_string()).collect::<Vec<_>>().join(",\n  ")
            );

            // Add appropriate unfolding around this old expression
            // Note: unfoldings must have no effect on siblings
            let result = self.curr_bctxt.clone()
                .obtain_permissions(perms)
                .into_iter()
                .rev()
                .fold(
                    inner_expr,
                    |expr, action| action.to_expr(expr)
                );

            result
        };

        debug!("[exit] fold = {}", res);
        res
    }

    fn fold_func_app(
        &mut self,
        function_name: String,
        args: Vec<vir::Expr>,
        formal_args: Vec<vir::LocalVar>,
        return_type: vir::Type,
        position: vir::Position
    ) -> vir::Expr {
        if self.wait_old_expr {
            vir::Expr::FuncApp(
                function_name,
                args.into_iter().map(|e| self.fold(e)).collect(),
                formal_args.clone(),
                return_type.clone(),
                position.clone())
        } else {

            let func_app = vir::Expr::FuncApp(
                function_name,
                args,
                formal_args,
                return_type,
                position);

            trace!("[enter] fold_func_app {}", func_app);

            let perms: Vec<_> = func_app
                .get_required_permissions(self.curr_bctxt.predicates())
                .into_iter()
                .collect();

            let result = self.curr_bctxt.clone()
                .obtain_permissions(perms)
                .into_iter()
                .rev()
                .fold(
                    func_app,
                    |expr, action| action.to_expr(expr)
                );

            trace!("[exit] fold_func_app {}", result);
            result
        }
    }
}
