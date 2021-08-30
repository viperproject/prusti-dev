use std::mem;
use std::ops::Deref;

use log::*;

use prusti_common::report;
use prusti_common::utils::to_string::ToString;
use vir_crate::polymorphic::{self as vir, CfgReplacer};

use super::action::Action;
use super::borrows;
use super::FoldUnfold;
use super::FoldUnfoldError;
use super::path_ctxt::PathCtxt;

impl<'p, 'v: 'p, 'tcx: 'v> FoldUnfold<'p, 'v, 'tcx> {
    /// Generates Viper statements that expire all the borrows from the given `dag`. The
    /// `surrounding_pctxt` will be modified to reflect the path context after the borrows have
    /// been expired.
    pub(super) fn process_expire_borrows(
        &mut self,
        dag: &vir::borrows::DAG,
        surrounding_pctxt: &mut PathCtxt<'p>,
        surrounding_block_index: vir::CfgBlockIndex,
        new_cfg: &vir::CfgMethod,
        label: Option<&str>,
    ) -> Result<Vec<vir::Stmt>, FoldUnfoldError> {
        trace!("[enter] process_expire_borrows dag=[{:?}]", dag);

        let mut cfg = build_initial_cfg(dag);

        let mut final_pctxt: Vec<Option<PathCtxt>> = vec![None; cfg.basic_blocks.len()];

        for curr_block_index in 0..cfg.basic_blocks.len() {
            self.dump_debug_info(dag, &cfg, surrounding_block_index, curr_block_index);

            let (mut pctxt, curr_block_pre_statements) = self.construct_initial_pctxt(
                dag,
                &mut cfg,
                surrounding_pctxt,
                surrounding_block_index,
                new_cfg,
                curr_block_index,
                &final_pctxt)?;

            let curr_block = &mut cfg.basic_blocks[curr_block_index];
            curr_block.statements.extend(curr_block_pre_statements);

            self.process_node(
                surrounding_pctxt,
                surrounding_block_index,
                new_cfg,
                curr_block,
                curr_block_index,
                label,
                &mut pctxt)?;

            final_pctxt[curr_block_index] = Some(pctxt);
        }

        // Merge all pctxts with reborrowed_nodes.is_empty() into one.
        *surrounding_pctxt = self.construct_final_pctxt(dag, &mut cfg, &final_pctxt)?;

        Ok(self.generate_final_statements(&cfg, label))
    }

    fn construct_initial_pctxt(&mut self,
        dag: &vir::borrows::DAG,
        cfg: &mut borrows::CFG,
        surrounding_pctxt: &mut PathCtxt<'p>,
        surrounding_block_index: vir::CfgBlockIndex,
        new_cfg: &vir::CfgMethod,
        curr_block_index: usize,
        final_pctxt: &[Option<PathCtxt<'p>>],
    ) -> Result<(PathCtxt<'p>, Vec<vir::Stmt>), FoldUnfoldError> {
        let curr_block = &cfg.basic_blocks[curr_block_index];
        Ok(if curr_block.predecessors.is_empty() {
            self.construct_initial_pctxt_no_predecessors(
                dag, cfg,
                surrounding_pctxt,
                surrounding_block_index,
                new_cfg,
                curr_block_index)?
        } else {
            let pctxt = self.construct_initial_pctxt_with_predecessors(
                dag, cfg,
                surrounding_pctxt,
                surrounding_block_index,
                new_cfg,
                curr_block_index,
                final_pctxt)?;
            (pctxt, Vec::new())
        })
    }

    fn construct_initial_pctxt_no_predecessors(&mut self,
        dag: &vir::borrows::DAG,
        cfg: &mut borrows::CFG,
        surrounding_pctxt: &mut PathCtxt<'p>,
        surrounding_block_index: vir::CfgBlockIndex,
        new_cfg: &vir::CfgMethod,
        curr_block_index: usize,
    ) -> Result<(PathCtxt<'p>, Vec<vir::Stmt>), FoldUnfoldError> {
        let curr_block = &cfg.basic_blocks[curr_block_index];
        let curr_node = &curr_block.node;
        let mut pctxt = surrounding_pctxt.clone();
        let mut curr_block_pre_statements = Vec::new();
        let end_block = surrounding_block_index;
        let start_block = self.get_cfg_block_of_last_borrow(
            surrounding_block_index, &curr_node.borrow);
        if !start_block.weak_eq(&end_block) {
            let path = new_cfg.find_path(start_block, end_block).unwrap();
            debug!(
                "process_expire_borrows borrow={:?} path={:?}",
                curr_node.borrow, path
            );
            let dropped_permissions = surrounding_pctxt
                .log()
                .collect_dropped_permissions(&path, dag);
            debug!(
                "process_expire_borrows borrow={:?} dropped_permissions={:?}",
                curr_node.borrow, dropped_permissions
            );
            for perm in &dropped_permissions {
                let comment = format!("restored (from log): {}", perm);
                curr_block_pre_statements.push(vir::Stmt::comment(comment));
            }
            pctxt
                .mut_state()
                .restore_dropped_perms(dropped_permissions.into_iter())?;
        }
        Ok((pctxt, curr_block_pre_statements))
    }

    fn construct_initial_pctxt_with_predecessors(&mut self,
        dag: &vir::borrows::DAG,
        cfg: &mut borrows::CFG,
        surrounding_pctxt: &mut PathCtxt<'p>,
        surrounding_block_index: vir::CfgBlockIndex,
        new_cfg: &vir::CfgMethod,
        curr_block_index: usize,
        final_pctxt: &[Option<PathCtxt<'p>>],
    ) -> Result<PathCtxt<'p>, FoldUnfoldError> {
        let curr_block = &cfg.basic_blocks[curr_block_index];
        let curr_node = &curr_block.node;
        let mut incoming_pctxt = Vec::new();
        for &predecessor in &curr_block.predecessors {
            let mut pctxt = final_pctxt[predecessor].as_ref().unwrap().clone();
            let predecessor_node = &cfg.basic_blocks[predecessor].node;
            let end_block = self.get_cfg_block_of_last_borrow(
                surrounding_block_index,
                &predecessor_node.borrow,
            );
            let start_block = self
                .get_cfg_block_of_last_borrow(surrounding_block_index, &curr_node.borrow);
            if start_block != end_block {
                let path = new_cfg.find_path(start_block, end_block).unwrap();
                debug!(
                    "process_expire_borrows borrow={:?} path={:?}",
                    curr_node.borrow, path
                );
                let dropped_permissions = surrounding_pctxt
                    .log()
                    .collect_dropped_permissions(&path, dag);
                debug!(
                    "process_expire_borrows borrow={:?} dropped_permissions={}",
                    curr_node.borrow,
                    dropped_permissions.iter().to_string()
                );
                for perm in &dropped_permissions {
                    let comment = format!("restored (from log): {}", perm);
                    let key = (predecessor, curr_block_index);
                    let entry = cfg.edges.entry(key).or_insert(Vec::new());
                    entry.push(vir::Stmt::comment(comment));
                }
                pctxt
                    .mut_state()
                    .restore_dropped_perms(dropped_permissions.into_iter())?;
            }
            incoming_pctxt.push(pctxt);
        }
        let incoming_pctxt_refs = incoming_pctxt.iter().collect();
        let (actions, mut pctxt) = self.prepend_join(incoming_pctxt_refs)?;
        for (&src_index, action) in curr_block.predecessors.iter().zip(&actions) {
            assert!(src_index < curr_block_index);
            if !action.is_empty() {
                //let stmts_to_add = action.iter().map(|a| a.to_stmt()).collect();
                let mut stmts_to_add = Vec::new();
                for a in &action.0 {
                    stmts_to_add.push(a.to_stmt());
                    if let Action::Drop(perm, missing_perm) = a {
                        if dag.in_borrowed_places(missing_perm.get_place())
                            && perm.get_perm_amount() != vir::PermAmount::Read
                        {
                            let comment = vir::Stmt::comment(format!(
                                "restored (in branch merge): {} ({})",
                                perm, missing_perm
                            ));
                            stmts_to_add.push(comment);
                            pctxt.mut_state().restore_dropped_perm(perm.clone())?;
                        }
                    }
                }
                let key = (src_index, curr_block_index);
                let entry = cfg.edges.entry(key).or_insert(Vec::new());
                entry.extend(stmts_to_add);
            }
        }
        Ok(pctxt)
    }

    fn process_node(&mut self,
        surrounding_pctxt: &mut PathCtxt<'p>,
        surrounding_block_index: vir::CfgBlockIndex,
        new_cfg: &vir::CfgMethod,
        curr_block: &mut borrows::BasicBlock,
        curr_block_index: usize,
        label: Option<&str>,
        pctxt: &mut PathCtxt<'p>
    ) -> Result<(), FoldUnfoldError> {
        let curr_node = &curr_block.node;
        trace!("process_node: {:?}", curr_node);
        for s in &curr_node.stmts {
            trace!("stmt: {}", s);
        }

        for (stmt_index, stmt) in curr_node.stmts.iter().enumerate() {
            debug!(
                "process_expire_borrows block={} ({:?}) stmt={}",
                curr_block_index, curr_node.borrow, stmt
            );
            let new_stmts = self.replace_stmt(
                stmt_index,
                &stmt,
                false,
                pctxt,
                surrounding_block_index,
                new_cfg,
                label,
            )?;
            curr_block.statements.extend(new_stmts);
        }

        // Remove read permissions.
        let duplicated_perms = surrounding_pctxt
            .log()
            .get_duplicated_read_permissions(curr_node.borrow);
        let mut maybe_original_place = None;
        for (mut read_access, original_place) in duplicated_perms {
            if let Some(ref place) = curr_node.place {
                debug!(
                    "place={} original_place={} read_access={}",
                    place, original_place, read_access
                );
                read_access = read_access.replace_place(&original_place, place);
            }
            maybe_original_place = Some(original_place);
            let stmt = vir::Stmt::Exhale( vir::Exhale {
                expr: read_access,
                position: self.method_pos,
            });
            let new_stmts = self.replace_stmt(
                curr_block.statements.len(),
                &stmt,
                false,
                pctxt,
                surrounding_block_index,
                new_cfg,
                label,
            )?;
            curr_block.statements.extend(new_stmts);
        }
        if let Some(original_place) = maybe_original_place {
            if pctxt.state().contains_acc(&original_place) {
                pctxt.mut_state().insert_moved(original_place);
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
        debug!(
            "curr_node.alive_conflicting_borrows={:?}",
            curr_node.alive_conflicting_borrows
        );
        debug!(
            "curr_node.conflicting_borrows={:?}",
            curr_node.conflicting_borrows
        );
        if curr_node.alive_conflicting_borrows.is_empty() {
            for &borrow in &curr_node.conflicting_borrows {
                curr_block
                    .statements
                    .extend(self.restore_write_permissions(borrow, pctxt)?);
            }
            curr_block
                .statements
                .extend(self.restore_write_permissions(curr_node.borrow, pctxt)?);
        }
        debug!(
            "curr_node.alive_conflicting_borrows={:?}",
            curr_node.alive_conflicting_borrows
        );
        debug!(
            "curr_node.conflicting_borrows={:?}",
            curr_node.conflicting_borrows
        );

        Ok(())
    }

    fn construct_final_pctxt(&mut self,
        dag: &vir::borrows::DAG,
        cfg: &mut borrows::CFG,
        final_pctxt: &[Option<PathCtxt<'p>>]
    ) -> Result<PathCtxt<'p>, FoldUnfoldError> {
        let final_blocks: Vec<_> = cfg
            .basic_blocks
            .iter()
            .enumerate()
            .filter(|(_, block)| block.successors.is_empty())
            .map(|(i, _)| i)
            .collect();
        let final_pctxts: Vec<_> = final_blocks
            .iter()
            .map(|i| final_pctxt[*i].as_ref().unwrap())
            .collect();
        let (actions, mut final_pctxt) = self.prepend_join(final_pctxts)?;
        for (&i, action) in final_blocks.iter().zip(actions.iter()) {
            if !action.is_empty() {
                let mut stmts_to_add = Vec::new();
                for a in action.deref() {
                    stmts_to_add.push(a.to_stmt());
                    if let Action::Drop(perm, missing_perm) = a {
                        if dag.in_borrowed_places(missing_perm.get_place())
                            && perm.get_perm_amount() != vir::PermAmount::Read
                        {
                            let comment =
                                format!("restored (in branch merge): {} ({})", perm, missing_perm);
                            stmts_to_add.push(vir::Stmt::comment(comment));
                            final_pctxt.mut_state().restore_dropped_perm(perm.clone())?;
                        }
                    }
                }
                //let stmts_to_add = action.iter().map(|a| a.to_stmt());
                cfg.basic_blocks[i].statements.extend(stmts_to_add);
            }
        }
        Ok(final_pctxt)
    }

    fn generate_final_statements(&mut self,
        cfg: &borrows::CFG,
        label: Option<&str>,
    ) -> Vec<vir::Stmt> {
        let mut stmts = Vec::new();
        for (i, block) in cfg.basic_blocks.iter().enumerate() {
            stmts.push(vir::Stmt::If( vir::If {
                guard: block.guard.clone(),
                then_stmts: self.patch_places(&block.statements, label),
                else_stmts: vec![]
            }));
            for ((from, to), statements) in &cfg.edges {
                if *from == i {
                    let condition = vir::Expr::and(
                        block.guard.clone(),
                        cfg.basic_blocks[*to].current_guard.clone(),
                    );
                    stmts.push(vir::Stmt::If( vir::If {
                        guard: condition,
                        then_stmts: self.patch_places(statements, label),
                        else_stmts: vec![],
                    }));
                }
            }
        }
        stmts
    }

    fn dump_debug_info(&self,
        dag: &vir::borrows::DAG,
        cfg: &borrows::CFG,
        surrounding_block_index: vir::CfgBlockIndex,
        curr_block_index: usize
    ) {
        if !self.dump_debug_info { return; }
        let source_path = self.encoder.env().source_path();
        let source_filename = source_path.file_name().unwrap().to_str().unwrap();
        report::log::report_with_writer(
            "graphviz_reborrowing_dag_during_foldunfold",
            format!(
                "{}.{:?}.{}.dot",
                source_filename,
                dag,
                surrounding_block_index.index()
            ),
            |writer| cfg.to_graphviz(writer, curr_block_index),
        );
    }
}

fn build_initial_cfg(dag: &vir::borrows::DAG) -> borrows::CFG {
    let mut cfg = borrows::CFG::new();
    for node in dag.iter() {
        trace!("process_expire_borrows construct cfg node={:?}", node);
        let predecessors = node
            .reborrowing_nodes
            .iter()
            .map(|b| dag.get_borrow_index(*b))
            .collect();
        let successors = node
            .reborrowed_nodes
            .iter()
            .map(|b| dag.get_borrow_index(*b))
            .collect();
        let guard = dag.guard(node.borrow);
        let current_guard = node.guard.clone();
        let statements = vec![vir::Stmt::comment(format!("expire loan {:?}", node.borrow))];
        let block = borrows::BasicBlock {
            node,
            guard, current_guard,
            predecessors, successors,
            statements,
        };
        cfg.add_block(block);
    }
    cfg
}
