// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use self::path_ctxt::*;
use crate::encoder::{
    foldunfold::{action::Action, footprint::*, perm::*, requirements::*, semantics::ApplyOnState},
    Encoder,
};
#[rustfmt::skip]
use ::log::{debug, trace};
use super::errors::SpannedEncodingError;
use crate::encoder::high::types::HighTypeEncoderInterface;
use prusti_common::{config, report, utils::to_string::ToString, vir::ToGraphViz, Stopwatch};
use prusti_rustc_interface::middle::mir;
use rustc_hash::{FxHashMap, FxHashSet};
use std::{self, fmt, ops::Deref};
use vir_crate::{
    polymorphic as vir,
    polymorphic::{
        borrows::Borrow, CfgBlockIndex, CfgReplacer, CheckNoOpAction, FallibleExprFolder,
        PermAmount, PermAmountError,
    },
};

mod action;
mod borrows;
mod footprint;
mod log;
mod path_ctxt;
mod perm;
mod places_utils;
mod process_expire_borrows;
mod requirements;
mod semantics;
mod state;

pub type Predicates = FxHashMap<vir::Type, vir::Predicate>;

#[derive(Clone, Debug)]
pub enum FoldUnfoldError {
    /// The algorithm failed to obtain a permission
    FailedToObtain(Perm),
    /// The algorithm tried to generate a "folding .. in .." Viper expression
    RequiresFolding(
        vir::Type,
        Vec<vir::Expr>,
        PermAmount,
        vir::MaybeEnumVariantIndex,
        vir::Position,
    ),
    /// The algorithm tried to add permissions in an invalid way.
    InvalidPermAmountAdd(String),
    /// The algorithm tried to add permissions in an invalid way.
    InvalidPermAmountSub(String),
    /// The algorithm couldn' find a predicate definition.
    MissingPredicate(vir::Type),
    /// The algorithms tried to remove a predicate that is not in the
    /// fold-unfold state.
    FailedToRemovePred(vir::Expr, PermAmount),
    /// The algorithm tried to lookup a never-seen-before label
    MissingLabel(String),
    /// Other encoding error.
    SpannedEncodingError(SpannedEncodingError),
    /// Unsupported feature
    Unsupported(String),
}

impl fmt::Display for FoldUnfoldError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FoldUnfoldError::FailedToObtain(perm) => {
                writeln!(f, "The required permission {perm} cannot be obtained.")
            }
            FoldUnfoldError::RequiresFolding(_pred, args, frac, _variant, _pos) => {
                writeln!(f,
                    "A pure expression needs to fold Pred({}, {}), but Viper doesn't support 'folding .. in ..' expressions.",
                    args[0],
                    frac
                )
            }
            FoldUnfoldError::InvalidPermAmountAdd(error) => {
                writeln!(f, "Failed to add fractional permissions: {error}.")
            }
            FoldUnfoldError::InvalidPermAmountSub(error) => {
                writeln!(f, "Failed to subtract fractional permissions: {error}.")
            }
            FoldUnfoldError::MissingPredicate(pred) => {
                writeln!(f, "The predicate definition of {pred} is not available.")
            }
            FoldUnfoldError::FailedToRemovePred(expr, frac) => {
                writeln!(
                    f,
                    "Tried to exhale a Pred({expr}, {frac}) permission that is not available."
                )
            }
            FoldUnfoldError::MissingLabel(label) => {
                writeln!(
                    f,
                    "An old[{label}](..) expression uses a label that has not been declared."
                )
            }
            FoldUnfoldError::SpannedEncodingError(error) => {
                writeln!(f, "Encoding error: {error:?}")
            }
            FoldUnfoldError::Unsupported(error) => {
                writeln!(f, "Unsupported feature: {error}.")
            }
        }
    }
}

impl From<PermAmountError> for FoldUnfoldError {
    fn from(err: PermAmountError) -> Self {
        match err {
            PermAmountError::InvalidAdd(a, b) => {
                FoldUnfoldError::InvalidPermAmountAdd(format!("invalid addition: {a} + {b}"))
            }
            PermAmountError::InvalidSub(a, b) => {
                FoldUnfoldError::InvalidPermAmountSub(format!("invalid substraction: {a} - {b}"))
            }
        }
    }
}

impl From<SpannedEncodingError> for FoldUnfoldError {
    fn from(err: SpannedEncodingError) -> Self {
        Self::SpannedEncodingError(err)
    }
}

fn add_unfolding_to_expr(expr: vir::Expr, pctxt: &PathCtxt) -> Result<vir::Expr, FoldUnfoldError> {
    let pctxt_at_label = FxHashMap::default();
    // First, add unfolding only inside old expressions
    let expr = ExprReplacer::new(pctxt.clone(), &pctxt_at_label, true).fallible_fold(expr)?;
    // Then, add unfolding expressions everywhere else
    ExprReplacer::new(pctxt.clone(), &pctxt_at_label, false).fallible_fold(expr)
}

pub fn add_folding_unfolding_to_function(
    function: vir::Function,
    predicates: FxHashMap<vir::Type, vir::Predicate>,
) -> Result<vir::Function, FoldUnfoldError> {
    if config::dump_debug_info() {
        prusti_common::report::log::report(
            "vir_function_before_foldunfold",
            format!("{}.vir", function.name),
            &function,
        );
    }

    // Compute inner state
    let formal_vars = function.formal_args.clone();
    // Viper functions cannot contain label statements, so knowing all usages of old expressions
    // is not needed.
    let old_exprs = FxHashMap::default();
    let mut pctxt = PathCtxt::new(formal_vars, &predicates, &old_exprs);
    for pre in &function.pres {
        pctxt.apply_stmt(&vir::Stmt::Inhale(vir::Inhale { expr: pre.clone() }))?;
    }
    // Add appropriate unfolding around expressions
    let result = vir::Function {
        pres: function
            .pres
            .into_iter()
            .map(|e| add_unfolding_to_expr(e, &pctxt))
            .collect::<Result<_, FoldUnfoldError>>()?,
        posts: function
            .posts
            .into_iter()
            .map(|e| add_unfolding_to_expr(e, &pctxt))
            .collect::<Result<_, FoldUnfoldError>>()?,
        body: function
            .body
            .map(|e| add_unfolding_to_expr(e, &pctxt))
            .map_or(Ok(None), |r| r.map(Some))?,
        ..function
    };

    if config::dump_debug_info() {
        prusti_common::report::log::report(
            "vir_function_after_foldunfold",
            format!("{}.dot", result.name),
            &result,
        );
    }

    Ok(result)
}

#[tracing::instrument(level = "debug", skip_all)]
pub fn add_fold_unfold<'p, 'v: 'p, 'tcx: 'v>(
    encoder: &'p Encoder<'v, 'tcx>,
    cfg: vir::CfgMethod,
    borrow_locations: &'p FxHashMap<Borrow, mir::Location>,
    cfg_map: &'p FxHashMap<mir::BasicBlock, FxHashSet<CfgBlockIndex>>,
    method_pos: vir::Position,
) -> Result<vir::CfgMethod, FoldUnfoldError> {
    let _stopwatch =
        Stopwatch::start_debug("prusti-client", "add fold-unfold statements to a method");
    let cfg_vars = cfg.get_all_vars();
    let predicates = encoder.get_used_viper_predicates_map()?;
    // Collect all old expressions used in the CFG
    let old_exprs = {
        struct OldExprCollector {
            old_exprs: FxHashMap<String, Vec<vir::Expr>>,
        }
        impl vir::ExprWalker for OldExprCollector {
            #[tracing::instrument(level = "trace", skip(self))]
            fn walk_labelled_old(
                &mut self,
                vir::LabelledOld {
                    label, box base, ..
                }: &vir::LabelledOld,
            ) {
                self.old_exprs
                    .entry(label.to_string())
                    .or_default()
                    .push(base.clone());
                // Recurse, in case old expressions are nested
                self.walk(base);
            }
        }
        impl vir::StmtWalker for OldExprCollector {
            fn walk_expr(&mut self, expr: &vir::Expr) {
                vir::ExprWalker::walk(self, expr);
            }
            // We also need to collect old expressions inside ReborrowingDAGs
            fn walk_expire_borrows(&mut self, expire_borrows: &vir::ExpireBorrows) {
                for node in expire_borrows.dag.iter() {
                    for stmt in &node.stmts {
                        vir::StmtWalker::walk(self, stmt);
                    }
                }
            }
        }
        let mut old_expr_collector = OldExprCollector {
            old_exprs: FxHashMap::default(),
        };
        cfg.walk_statements(|stmt| vir::StmtWalker::walk(&mut old_expr_collector, stmt));
        old_expr_collector.old_exprs
    };
    let initial_pctxt = PathCtxt::new(cfg_vars, &predicates, &old_exprs);
    FoldUnfold::new(
        encoder,
        initial_pctxt,
        &cfg,
        borrow_locations,
        cfg_map,
        method_pos,
    )
    .replace_cfg(&cfg)
}

#[derive(Clone)]
struct FoldUnfold<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p Encoder<'v, 'tcx>,
    initial_pctxt: PathCtxt<'p>,
    pctxt_at_label: FxHashMap<String, PathCtxt<'p>>,
    dump_debug_info: bool,
    /// Used for debugging the dump
    foldunfold_state_filter: String,
    /// Generate additional assertions to check that the state of the fold-unfold algorithm
    /// under-approximates the set of permissions actually available in Viper.
    check_foldunfold_state: bool,
    /// The orignal CFG
    cfg: &'p vir::CfgMethod,
    borrow_locations: &'p FxHashMap<vir::borrows::Borrow, mir::Location>,
    cfg_map: &'p FxHashMap<mir::BasicBlock, FxHashSet<CfgBlockIndex>>,
    method_pos: vir::Position,
}

impl<'p, 'v: 'p, 'tcx: 'v> FoldUnfold<'p, 'v, 'tcx> {
    pub fn new(
        encoder: &'p Encoder<'v, 'tcx>,
        initial_pctxt: PathCtxt<'p>,
        cfg: &'p vir::CfgMethod,
        borrow_locations: &'p FxHashMap<vir::borrows::Borrow, mir::Location>,
        cfg_map: &'p FxHashMap<mir::BasicBlock, FxHashSet<CfgBlockIndex>>,
        method_pos: vir::Position,
    ) -> Self {
        FoldUnfold {
            encoder,
            initial_pctxt,
            pctxt_at_label: FxHashMap::default(),
            dump_debug_info: config::dump_debug_info_during_fold(),
            check_foldunfold_state: config::check_foldunfold_state(),
            foldunfold_state_filter: config::foldunfold_state_filter(),
            cfg,
            borrow_locations,
            cfg_map,
            method_pos,
        }
    }

    fn replace_expr(
        &self,
        expr: &vir::Expr,
        curr_pctxt: &PathCtxt<'p>,
    ) -> Result<vir::Expr, FoldUnfoldError> {
        ExprReplacer::new(curr_pctxt.clone(), &self.pctxt_at_label, false)
            .fallible_fold(expr.clone())
    }

    #[tracing::instrument(level = "trace", skip(self))]
    fn replace_old_expr(
        &self,
        expr: &vir::Expr,
        curr_pctxt: &PathCtxt<'p>,
    ) -> Result<vir::Expr, FoldUnfoldError> {
        ExprReplacer::new(curr_pctxt.clone(), &self.pctxt_at_label, true)
            .fallible_fold(expr.clone())
    }

    /// Insert "unfolding in" in old expressions
    #[tracing::instrument(level = "trace", skip(self), ret)]
    fn rewrite_stmt_with_unfoldings_in_old(
        &self,
        stmt: vir::Stmt,
        pctxt: &PathCtxt<'p>,
    ) -> Result<vir::Stmt, FoldUnfoldError> {
        stmt.fallible_map_expr(|e| self.replace_old_expr(&e, pctxt))
    }

    /// Insert "unfolding in" expressions
    fn rewrite_stmt_with_unfoldings(
        &self,
        stmt: vir::Stmt,
        pctxt: &PathCtxt<'p>,
    ) -> Result<vir::Stmt, FoldUnfoldError> {
        match stmt {
            vir::Stmt::Inhale(vir::Inhale { expr }) => {
                // Compute inner state
                let mut inner_pctxt = pctxt.clone();
                let inner_state = inner_pctxt.mut_state();
                inner_state.insert_all_perms(
                    expr.get_footprint(pctxt.predicates())
                        .into_iter()
                        .filter(|p| !p.get_place().is_local() && p.is_curr()),
                )?;

                // Rewrite statement
                Ok(vir::Stmt::Inhale(vir::Inhale {
                    expr: self.replace_expr(&expr, &inner_pctxt)?,
                }))
            }
            vir::Stmt::TransferPerm(vir::TransferPerm {
                left,
                right,
                unchecked,
            }) => {
                // Compute rhs state
                let rhs_pctxt = pctxt.clone();
                /*
                let rhs_state = rhs_pctxt.mut_state();
                rhs_state.insert_all_perms(
                    rhs.get_footprint(pctxt.predicates())
                        .into_iter()
                        .filter(|p| p.is_pred())
                )?;
                */
                let new_lhs = if unchecked {
                    left
                } else {
                    self.replace_expr(&left, pctxt)?
                };

                // Rewrite statement
                Ok(vir::Stmt::TransferPerm(vir::TransferPerm {
                    left: new_lhs,
                    right: self.replace_old_expr(&right, &rhs_pctxt)?,
                    unchecked,
                }))
            }
            vir::Stmt::PackageMagicWand(vir::PackageMagicWand {
                magic_wand,
                package_stmts,
                label,
                variables,
                position,
            }) => Ok(vir::Stmt::PackageMagicWand(vir::PackageMagicWand {
                magic_wand: self.replace_expr(&magic_wand, pctxt)?,
                package_stmts,
                label,
                variables,
                position,
            })),
            _ => stmt.fallible_map_expr(|e| self.replace_expr(&e, pctxt)),
        }
    }

    fn get_cfg_block_of_last_borrow(
        &self,
        curr_block: CfgBlockIndex,
        borrow: &Borrow,
    ) -> CfgBlockIndex {
        let mir_location = self.borrow_locations[borrow];
        let borrow_creation = &self.cfg_map[&mir_location.block];
        // HACK: Choose the closest block. Can be optimized.
        let mut nearest_block = None;
        for &block in borrow_creation {
            if let Some(path) = self.cfg.find_path(block, curr_block) {
                if let Some((_, distance)) = nearest_block {
                    if distance > path.len() {
                        nearest_block = Some((block, path.len()));
                    }
                } else {
                    nearest_block = Some((block, path.len()));
                }
            }
        }
        assert!(
            nearest_block.is_some(),
            "Could not find a predecessor of {curr_block:?} in the blocks that create the borrow {borrow:?} ({borrow_creation:?})",
        );
        nearest_block.unwrap().0
    }
}

#[derive(Debug)]
pub(super) struct ActionVec(pub Vec<Action>);

impl Deref for ActionVec {
    type Target = Vec<Action>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

// TODO: get rid of newtype wrapper when rust updated to 1.41.0+, where the orphan rules are relaxed to allow things like this
impl CheckNoOpAction for ActionVec {
    fn is_noop(&self) -> bool {
        self.is_empty()
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> vir::CfgReplacer<PathCtxt<'p>, ActionVec> for FoldUnfold<'p, 'v, 'tcx> {
    type Error = FoldUnfoldError;

    /// Dump the current CFG, for debugging purposes
    fn current_cfg(
        &self,
        new_cfg: &vir::CfgMethod,
        initial_pctxt: &[Option<PathCtxt>],
        _final_pctxt: &[Option<PathCtxt>],
    ) {
        if self.dump_debug_info {
            let source_path = self.encoder.env().name.source_path();
            let source_filename = source_path.file_name().unwrap().to_str().unwrap();
            let method_name = new_cfg.name();
            report::log::report_with_writer(
                "graphviz_method_during_foldunfold",
                format!("{source_filename}.{method_name}.dot"),
                |writer| {
                    new_cfg.to_graphviz_with_extra(writer, |bb_index| {
                        initial_pctxt
                            .get(bb_index)
                            .and_then(|opt_pctxt| {
                                opt_pctxt.as_ref().map(|pctxt| {
                                    let mut acc = pctxt.state().display_acc();
                                    let mut pred = pctxt.state().display_pred();
                                    if !self.foldunfold_state_filter.is_empty() {
                                        let filter = &self.foldunfold_state_filter;
                                        acc = acc
                                            .split('\n')
                                            .filter(|x| x.contains(filter))
                                            .map(|x| x.to_string())
                                            .collect::<Vec<_>>()
                                            .join("\n");
                                        pred = pred
                                            .split('\n')
                                            .filter(|x| x.contains(filter))
                                            .map(|x| x.to_string())
                                            .collect::<Vec<_>>()
                                            .join("\n");
                                    }
                                    vec![format!("Acc:\n{acc}"), format!("Pred:\n{pred}")]
                                })
                            })
                            .unwrap_or_default()
                    })
                },
            );
        }
    }

    fn check_compatible_back_edge(_left: &PathCtxt<'p>, _right: &PathCtxt<'p>) {
        //let left_state = left.state();
        //let right_state = right.state();

        // TODO: re-enable this consistency check, discarding all places for which `.is_simple_place()` is false
        //debug_assert_eq!(left_state.acc(), right_state.acc(), "back edge (acc)");
        //debug_assert_eq!(left_state.pred(), right_state.pred(), "back edge (pred)");
        //debug_assert_eq!(left_state.framing_stack(), right_state.framing_stack(), "back edge (framing)");
    }

    /// Give the initial branch context
    fn initial_context(&mut self) -> Result<PathCtxt<'p>, Self::Error> {
        Ok(self.initial_pctxt.clone())
    }

    /// Replace some statements, mutating the branch context
    #[allow(clippy::too_many_arguments)]
    #[tracing::instrument(level = "debug", skip(self, pctxt, new_cfg, stmt), fields(stmt = %stmt))]
    fn replace_stmt(
        &mut self,
        stmt_index: usize,
        stmt: &vir::Stmt,
        is_last_before_return: bool,
        pctxt: &mut PathCtxt<'p>,
        curr_block_index: vir::CfgBlockIndex,
        new_cfg: &vir::CfgMethod,
        label: Option<&str>,
    ) -> Result<Vec<vir::Stmt>, Self::Error> {
        if let vir::Stmt::ExpireBorrows(vir::ExpireBorrows { ref dag }) = stmt {
            let mut stmts = vec![vir::Stmt::comment(format!("{stmt}"))];
            trace!("State acc {{\n{}\n}}", pctxt.state().display_acc());
            trace!("State pred {{\n{}\n}}", pctxt.state().display_pred());
            trace!("State moved {{\n{}\n}}", pctxt.state().display_moved());
            let expire_borrow_statements =
                self.process_expire_borrows(dag, pctxt, curr_block_index, new_cfg, label)?;
            trace!("State acc {{\n{}\n}}", pctxt.state().display_acc());
            trace!("State pred {{\n{}\n}}", pctxt.state().display_pred());
            trace!("State moved {{\n{}\n}}", pctxt.state().display_moved());
            stmts.extend(expire_borrow_statements);
            return Ok(stmts);
        }

        let mut stmt = stmt.clone();

        // Store state for old[lhs] expressions
        match stmt {
            vir::Stmt::PackageMagicWand(vir::PackageMagicWand { ref magic_wand, .. })
            | vir::Stmt::ApplyMagicWand(vir::ApplyMagicWand { ref magic_wand, .. })
            | vir::Stmt::Inhale(vir::Inhale {
                expr: ref magic_wand,
                ..
            }) => {
                if let vir::Expr::MagicWand(vir::MagicWand { box ref left, .. }) = magic_wand {
                    // TODO: This should be done also for magic wand expressions inside inhale/exhale.
                    let label = "lhs".to_string();
                    let mut labelled_pctxt = pctxt.clone();
                    let labelled_state = labelled_pctxt.mut_state();
                    labelled_state.remove_all();
                    vir::Stmt::Inhale(vir::Inhale { expr: left.clone() })
                        .apply_on_state(labelled_state, pctxt.predicates())?;
                    if let vir::Expr::PredicateAccessPredicate(vir::PredicateAccessPredicate {
                        box ref argument,
                        permission,
                        ..
                    }) = left
                    {
                        labelled_state.insert_acc(argument.clone(), *permission)?;
                    }
                    labelled_state.replace_places(|place| place.old(&label));
                    self.pctxt_at_label
                        .insert(label.to_string(), labelled_pctxt);
                }
            }

            _ => {} // Nothing
        }

        let mut stmts: Vec<vir::Stmt> = vec![];

        if stmt_index == 0 && config::dump_path_ctxt_in_debug_info() {
            let acc_state = pctxt.state().display_acc().replace('\n', "\n//");
            stmts.push(vir::Stmt::comment(format!(
                "[state] acc: {{\n//{acc_state}\n//}}"
            )));
            let pred_state = pctxt.state().display_pred().replace('\n', "\n//");
            stmts.push(vir::Stmt::comment(format!(
                "[state] pred: {{\n//{pred_state}\n//}}"
            )));
            let moved_state = pctxt.state().display_moved().replace('\n', "\n//");
            stmts.push(vir::Stmt::comment(format!(
                "[state] moved: {{\n//{moved_state}\n//}}"
            )));
        }

        // 1. Insert "unfolding in" inside old expressions. This handles *old* requirements.
        trace!("[step.1] replace_stmt: {}", stmt);
        stmt = self.rewrite_stmt_with_unfoldings_in_old(stmt, pctxt)?;

        // 2. Obtain required *curr* permissions. *old* requirements will be handled at steps 0 and/or 4.
        trace!("[step.2] replace_stmt: {}", stmt);
        {
            let all_perms = stmt.get_required_permissions(pctxt.predicates());
            let pred_permissions: Vec<_> =
                all_perms.iter().cloned().filter(|p| p.is_pred()).collect();

            let acc_permissions: Vec<_> = all_perms
                .into_iter()
                .filter(|p| {
                    if !p.is_acc() {
                        false
                    } else if p.is_curr() {
                        true
                    } else {
                        pred_permissions
                            .iter()
                            .any(|pred_p| pred_p.get_place() == p.get_place())
                    }
                })
                .collect();

            let mut perms = acc_permissions;
            perms.extend(pred_permissions.into_iter());
            trace!(
                "required permissions: {{\n{}\n}}",
                perms
                    .iter()
                    .map(|x| format!("  {x:?}"))
                    .collect::<Vec<_>>()
                    .join(",\n")
            );

            if !perms.is_empty() {
                stmts.extend(pctxt.obtain_permissions(perms)?.iter().map(|a| a.to_stmt()));

                if self.check_foldunfold_state && !is_last_before_return && label.is_none() {
                    stmts.push(vir::Stmt::comment("Assert content of fold/unfold state"));
                    stmts.push(vir::Stmt::Assert(vir::Assert {
                        expr: pctxt.state().as_vir_expr(),
                        position: vir::Position::default(),
                    }));
                }
            }
        }

        // A label has to ensure that all usages of labelled-old expressions can be later
        // solved by *unfolding*, and not *folding*, permissions.
        // See issue https://github.com/viperproject/prusti-dev/issues/797.
        if let vir::Stmt::Label(label) = &stmt {
            let curr_acc_perms = pctxt.state().acc_places();
            let mut perms = pctxt
                .old_exprs()
                .get(&label.label)
                .map(|exprs| {
                    exprs
                        .iter()
                        .flat_map(|e| e.get_required_stmt_permissions(pctxt.predicates()))
                        .collect::<FxHashSet<_>>()
                })
                .unwrap_or_default();
            // Remove what would need to be unfolded
            perms.retain(|p| {
                p.is_pred()
                    && curr_acc_perms.iter().all(|q| {
                        q.get_place()
                            .map(|q_place| !p.has_proper_prefix(q_place))
                            .unwrap_or(true)
                    })
            });
            stmts.extend(
                pctxt
                    .obtain_permissions(perms.into_iter().collect())?
                    .iter()
                    .map(|a| a.to_stmt()),
            );
        }

        // 3. Replace special statements
        trace!("[step.3] replace_stmt: {}", stmt);
        stmt = match stmt {
            vir::Stmt::PackageMagicWand(vir::PackageMagicWand {
                magic_wand:
                    vir::Expr::MagicWand(vir::MagicWand {
                        box ref left,
                        box ref right,
                        ..
                    }),
                package_stmts: ref old_package_stmts,
                ref label,
                ref variables,
                ref position,
            }) => {
                let mut package_pctxt = pctxt.clone();
                let mut package_stmts = vec![];
                for stmt in old_package_stmts {
                    package_stmts.extend(self.replace_stmt(
                        stmt_index,
                        stmt,
                        false,
                        &mut package_pctxt,
                        curr_block_index,
                        new_cfg,
                        Some(label),
                    )?);
                    if config::dump_debug_info() {
                        //package_stmts.push(
                        //    vir::Stmt::comment(format!("[state] acc: {{\n{}\n}}", package_pctxt.state().display_acc()))
                        //);
                        //package_stmts.push(
                        //    vir::Stmt::comment(format!("[state] pred: {{\n{}\n}}", package_pctxt.state().display_pred()))
                        //);
                        report::log::report(
                            "vir_package",
                            "package.vir",
                            vir::Stmt::package_magic_wand(
                                left.clone(),
                                right.clone(),
                                package_stmts.clone(),
                                label.clone(),
                                variables.clone(),
                                *position,
                            ),
                        );
                    }
                }

                vir::Stmt::package_magic_wand(
                    left.clone(),
                    right.clone(),
                    package_stmts,
                    label.clone(),
                    variables.clone(),
                    *position,
                )
            }
            stmt => stmt,
        };

        // 4. Add "unfolding" expressions in statement. This handles *old* requirements.
        trace!("[step.4] replace_stmt: {}", stmt);
        stmt = self.rewrite_stmt_with_unfoldings(stmt, pctxt)?;

        // 5. Apply effect of statement on state
        trace!("[step.5] replace_stmt: {}", stmt);
        stmt = match stmt {
            vir::Stmt::If(vir::If {
                guard,
                then_stmts,
                else_stmts,
            }) => {
                let mut then_pctxt = pctxt.clone();
                let mut then_stmts = then_stmts
                    .into_iter()
                    .map(|stmt| {
                        self.replace_stmt(
                            stmt_index,
                            &stmt,
                            false,
                            &mut then_pctxt,
                            curr_block_index,
                            new_cfg,
                            None,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .flatten()
                    .collect::<Vec<_>>();
                let mut else_pctxt = pctxt.clone();
                let mut else_stmts = else_stmts
                    .into_iter()
                    .map(|stmt| {
                        self.replace_stmt(
                            stmt_index,
                            &stmt,
                            false,
                            &mut else_pctxt,
                            curr_block_index,
                            new_cfg,
                            None,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .flatten()
                    .collect::<Vec<_>>();
                let (mut join_actions, mut joined_pctxt) =
                    self.prepend_join(vec![&then_pctxt, &else_pctxt])?;
                else_stmts.extend(self.perform_prejoin_action(
                    &mut joined_pctxt,
                    curr_block_index,
                    join_actions.remove(1),
                )?);
                then_stmts.extend(self.perform_prejoin_action(
                    &mut joined_pctxt,
                    curr_block_index,
                    join_actions.remove(0),
                )?);
                *pctxt = joined_pctxt;
                vir::Stmt::If(vir::If {
                    guard,
                    then_stmts,
                    else_stmts,
                })
            }
            _ => {
                pctxt.apply_stmt(&stmt)?;
                stmt
            }
        };
        stmts.push(stmt.clone());

        // 6. Recombine permissions into full if read was carved out during fold.
        if let vir::Stmt::Inhale(vir::Inhale { expr }) = &stmt {
            // We may need to recombine predicates for which read permission was taking during
            // an unfold operation.
            let inhaled_places = expr.extract_predicate_places(vir::PermAmount::Read);
            let restorable_places: Vec<_> = pctxt
                .state()
                .pred()
                .iter()
                .filter(|(place, perm)| {
                    **perm == vir::PermAmount::Remaining
                        && inhaled_places.iter().any(|ip| place.has_prefix(ip))
                })
                .map(|(place, _)| place.clone())
                .collect();
            for place in restorable_places {
                let stmt = vir::Stmt::Obtain(vir::Obtain {
                    expr: vir::Expr::pred_permission(place, vir::PermAmount::Read).unwrap(),
                    position: vir::Position::default(), // This should trigger only unfolds,
                                                        // so the default position should be fine.
                });
                stmts.extend(self.replace_stmt(
                    stmt_index,
                    &stmt,
                    false,
                    pctxt,
                    curr_block_index,
                    new_cfg,
                    label,
                )?);
            }
        }

        // 7. Handle shared borrows.
        trace!("[step.6] replace_stmt: {}", stmt);
        if let vir::Stmt::Assign(vir::Assign {
            ref target,
            ref source,
            kind: vir::AssignKind::SharedBorrow(borrow),
        }) = stmt
        {
            // Check if in the state we have any write permissions
            // with the borrowed place as a prefix. If yes, change them
            // to read permissions and emit exhale acc(T(place), write-read).
            let mut acc_perm_counter = 0;
            let mut acc_perms: Vec<_> = pctxt
                .state()
                .acc()
                .iter()
                .filter(|&(place, perm_amount)| {
                    assert!(perm_amount.is_valid_for_specs());
                    place.has_prefix(source) && !place.is_local()
                })
                .map(|(place, perm_amount)| {
                    acc_perm_counter += 1;
                    (place.clone(), *perm_amount, acc_perm_counter)
                })
                .collect();
            acc_perms.sort_unstable_by(|(place1, _, id1), (place2, _, id2)| {
                let key1 = (place1.place_depth(), id1);
                let key2 = (place2.place_depth(), id2);
                key1.cmp(&key2)
            });
            trace!(
                "acc_perms = {}",
                acc_perms
                    .iter()
                    .map(|(a, p, id)| format!("({a}, {p}, {id}), "))
                    .collect::<String>()
            );
            for (place, perm_amount, _) in acc_perms {
                trace!("acc place: {} {}", place, perm_amount);
                trace!("rhs_place={} {:?}", source, pctxt.state().acc().get(source));
                trace!("lhs_place={} {:?}", target, pctxt.state().acc().get(target));
                if *source == place
                    && Some(&vir::PermAmount::Write) == pctxt.state().acc().get(target)
                {
                    // We are copying a shared reference, so we do not need to change
                    // the root of rhs.
                    trace!("Copy of a shared reference. Ignore.");
                    continue;
                }
                if perm_amount == vir::PermAmount::Write {
                    let access = vir::Expr::FieldAccessPredicate(vir::FieldAccessPredicate {
                        base: Box::new(place.clone()),
                        permission: vir::PermAmount::Remaining,
                        position: vir::Position::default(),
                    });
                    pctxt
                        .log_mut()
                        .log_convertion_to_read(borrow, access.clone());
                    let stmt = vir::Stmt::Exhale(vir::Exhale {
                        expr: access,
                        position: self.method_pos,
                    });
                    pctxt.apply_stmt(&stmt)?;
                    stmts.push(stmt);
                }
                let new_place = place.replace_place(source, target);
                trace!("    new place: {}", new_place);
                let lhs_read_access = vir::Expr::FieldAccessPredicate(vir::FieldAccessPredicate {
                    base: Box::new(new_place),
                    permission: vir::PermAmount::Read,
                    position: vir::Position::default(),
                });
                pctxt.log_mut().log_read_permission_duplication(
                    borrow,
                    lhs_read_access.clone(),
                    target.clone(),
                );
                let stmt = vir::Stmt::Inhale(vir::Inhale {
                    expr: lhs_read_access,
                });
                pctxt.apply_stmt(&stmt)?;
                stmts.push(stmt);
            }
            let pred_perms: Vec<_> = pctxt
                .state()
                .pred()
                .iter()
                .filter(|&(place, perm_amount)| {
                    assert!(perm_amount.is_valid_for_specs());
                    place.has_prefix(source)
                })
                .map(|(place, perm_amount)| (place.clone(), *perm_amount))
                .collect();
            for (place, perm_amount) in pred_perms {
                trace!("pred place: {} {}", place, perm_amount);
                let predicate_type = place.get_type().clone();
                if perm_amount == vir::PermAmount::Write {
                    let access =
                        vir::Expr::PredicateAccessPredicate(vir::PredicateAccessPredicate {
                            predicate_type: predicate_type.clone(),
                            argument: Box::new(place.clone()),
                            permission: vir::PermAmount::Remaining,
                            position: place.pos(),
                        });
                    pctxt
                        .log_mut()
                        .log_convertion_to_read(borrow, access.clone());
                    let stmt = vir::Stmt::Exhale(vir::Exhale {
                        expr: access,
                        position: self.method_pos,
                    });
                    pctxt.apply_stmt(&stmt)?;
                    stmts.push(stmt);
                }
                let new_place = place.replace_place(source, target);
                trace!("    new place: {}", new_place);
                let lhs_read_access =
                    vir::Expr::PredicateAccessPredicate(vir::PredicateAccessPredicate {
                        predicate_type,
                        argument: Box::new(new_place),
                        permission: vir::PermAmount::Read,
                        position: vir::Position::default(),
                    });
                pctxt.log_mut().log_read_permission_duplication(
                    borrow,
                    lhs_read_access.clone(),
                    target.clone(),
                );
                let stmt = vir::Stmt::Inhale(vir::Inhale {
                    expr: lhs_read_access,
                });
                pctxt.apply_stmt(&stmt)?;
                stmts.push(stmt);
            }
        }

        // Store state for old expressions
        if let vir::Stmt::Label(vir::Label { ref label }) = stmt {
            let mut labelled_pctxt = pctxt.clone();
            let labelled_state = labelled_pctxt.mut_state();
            labelled_state.replace_places(|place| place.old(label));
            self.pctxt_at_label
                .insert(label.to_string(), labelled_pctxt);
        }

        // Delete lhs state
        self.pctxt_at_label.remove("lhs");

        debug!(
            "[exit] replace_stmt = [\n{}\n]",
            stmts
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
                .join("\n  ")
        );
        Ok(stmts)
    }

    /// Inject some statements and replace a successor, mutating the branch context
    #[tracing::instrument(level = "debug", skip(self, pctxt))]
    fn replace_successor(
        &mut self,
        succ: &vir::Successor,
        pctxt: &mut PathCtxt<'p>,
    ) -> Result<(Vec<vir::Stmt>, vir::Successor), Self::Error> {
        let exprs: Vec<&vir::Expr> =
            if let vir::Successor::GotoSwitch(ref guarded_targets, _) = succ {
                guarded_targets.iter().map(|g| &g.0).collect()
            } else {
                vec![]
            };

        let grouped_perms: FxHashMap<_, _> = exprs
            .iter()
            .flat_map(|e| e.get_required_stmt_permissions(pctxt.predicates()))
            .group_by_label();

        let mut stmts: Vec<vir::Stmt> = vec![];

        let mut some_perms_required = false;
        for (label, perms) in grouped_perms.into_iter() {
            trace!("Obtain at label {:?} permissions {:?}", label, perms);
            // Hack: skip old permissions
            if label.is_some() {
                continue;
            }
            if !perms.is_empty() {
                some_perms_required = true;
                let mut opt_old_pctxt =
                    label.map(|label_name| self.pctxt_at_label.get(&label_name).unwrap().clone());
                let label_pctxt = opt_old_pctxt.as_mut().unwrap_or(pctxt);
                stmts.extend(
                    label_pctxt
                        .obtain_permissions(perms)?
                        .iter()
                        .map(|a| a.to_stmt())
                        .collect::<Vec<_>>(),
                );
            }
        }

        if some_perms_required && self.check_foldunfold_state {
            stmts.push(vir::Stmt::comment("Assert content of fold/unfold state"));
            stmts.push(vir::Stmt::Assert(vir::Assert {
                expr: pctxt.state().as_vir_expr(),
                position: vir::Position::default(),
            }));
        }

        // Add "fold/unfolding in" expressions in successor
        let repl_expr = |expr: &vir::Expr| -> Result<vir::Expr, FoldUnfoldError> {
            self.replace_expr(expr, pctxt)
        };

        let new_succ = match succ {
            vir::Successor::Undefined => vir::Successor::Undefined,
            vir::Successor::Return => vir::Successor::Return,
            vir::Successor::Goto(target) => vir::Successor::Goto(*target),
            vir::Successor::GotoSwitch(guarded_targets, default_target) => {
                vir::Successor::GotoSwitch(
                    guarded_targets
                        .iter()
                        .map(|(cond, targ)| repl_expr(cond).map(|expr| (expr, *targ)))
                        .collect::<Result<Vec<_>, _>>()?,
                    *default_target,
                )
            }
        };

        debug!(
            "[exit] replace_successor = {}, [\n{}\n]",
            new_succ,
            stmts
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
                .join("\n  "),
        );
        Ok((stmts, new_succ))
    }

    /// Compute actions that need to be performed before the join point,
    /// returning the merged branch context.
    fn prepend_join(
        &mut self,
        bcs: Vec<&PathCtxt<'p>>,
    ) -> Result<(Vec<ActionVec>, PathCtxt<'p>), Self::Error> {
        prepend_join(bcs)
    }

    /// Convert actions to statements and log them.
    fn perform_prejoin_action(
        &mut self,
        pctxt: &mut PathCtxt,
        block_index: CfgBlockIndex,
        actions: ActionVec,
    ) -> Result<Vec<vir::Stmt>, Self::Error> {
        let mut stmts = Vec::new();
        for action in actions.0 {
            stmts.push(action.to_stmt());
            pctxt.log_mut().log_prejoin_action(block_index, action);
        }
        Ok(stmts)
    }
}

#[tracing::instrument(level = "trace", skip_all, fields(bcs.len = %bcs.len()))]
pub(super) fn prepend_join<'p>(
    bcs: Vec<&PathCtxt<'p>>,
) -> Result<(Vec<ActionVec>, PathCtxt<'p>), FoldUnfoldError> {
    assert!(!bcs.is_empty());
    if bcs.len() == 1 {
        Ok((vec![ActionVec(vec![])], bcs[0].clone()))
    } else {
        // Define two subgroups
        let mid = bcs.len() / 2;
        let left_pctxts = &bcs[..mid];
        let right_pctxts = &bcs[mid..];

        // Join the subgroups
        let (left_actions_vec, mut left_pctxt) = prepend_join(left_pctxts.to_vec())?;
        let (right_actions_vec, right_pctxt) = prepend_join(right_pctxts.to_vec())?;

        // Join the recursive calls
        let (merge_actions_left, merge_actions_right) = left_pctxt.join(right_pctxt)?;
        let merged_pctxt = left_pctxt;

        let mut branch_actions_vec: Vec<ActionVec> = vec![];
        for mut left_actions in left_actions_vec {
            left_actions.0.extend(merge_actions_left.iter().cloned());
            branch_actions_vec.push(left_actions);
        }
        for mut right_actions in right_actions_vec {
            right_actions.0.extend(merge_actions_right.iter().cloned());
            branch_actions_vec.push(right_actions);
        }

        trace!(
            "[exit] prepend_join(..{}): {}",
            &bcs.len(),
            branch_actions_vec
                .iter()
                .map(|v| format!("[{}]", v.iter().to_sorted_multiline_string()))
                .to_string()
        );
        Ok((branch_actions_vec, merged_pctxt))
    }
}

struct ExprReplacer<'b, 'a: 'b> {
    curr_pctxt: PathCtxt<'a>,
    pctxt_at_label: &'b FxHashMap<String, PathCtxt<'a>>,
    lhs_pctxt: Option<PathCtxt<'a>>,
    wait_old_expr: bool,
}

impl<'b, 'a: 'b> ExprReplacer<'b, 'a> {
    pub fn new(
        curr_pctxt: PathCtxt<'a>,
        pctxt_at_label: &'b FxHashMap<String, PathCtxt<'a>>,
        wait_old_expr: bool,
    ) -> Self {
        ExprReplacer {
            curr_pctxt,
            pctxt_at_label,
            lhs_pctxt: None,
            wait_old_expr,
        }
    }
}

impl<'b, 'a: 'b> FallibleExprFolder for ExprReplacer<'b, 'a> {
    type Error = FoldUnfoldError;

    #[tracing::instrument(level = "trace", skip_all, fields(expr = %expr))]
    fn fallible_fold(&mut self, expr: vir::Expr) -> Result<vir::Expr, Self::Error> {
        let res = if self.wait_old_expr || !expr.is_pure() {
            vir::default_fallible_fold_expr(self, expr)?
        } else {
            // Compute the unfoldings to be generated around the expression
            let perms: Vec<_> = expr
                .get_required_expr_permissions(self.curr_pctxt.predicates())
                .into_iter()
                .collect();
            let unfolding_actions: Vec<_> = self
                .curr_pctxt
                .clone()
                .obtain_permissions(perms)?
                .into_iter()
                .collect();

            // Prepare the fold-unfold state used for the subexpressions
            let mut inner_pctxt = self.curr_pctxt.clone();
            let inner_state = inner_pctxt.mut_state();
            for action in &unfolding_actions {
                action
                    .to_stmt()
                    .apply_on_state(inner_state, self.curr_pctxt.predicates())?;
            }

            // Store state
            let mut tmp_curr_pctxt = inner_pctxt;
            std::mem::swap(&mut self.curr_pctxt, &mut tmp_curr_pctxt);

            // Add unfoldings in the subexpressions
            let inner_expr = vir::default_fallible_fold_expr(self, expr)?;

            // Restore state
            std::mem::swap(&mut self.curr_pctxt, &mut tmp_curr_pctxt);

            // Add the unfoldings that we computed above
            let mut result = inner_expr;
            for action in unfolding_actions.iter().rev() {
                result = action.to_expr(result)?;
            }

            result
        };

        trace!("[exit] fallible_fold = {}", res);
        Ok(res)
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn fallible_fold_unfolding(
        &mut self,
        vir::Unfolding {
            predicate,
            arguments,
            base,
            permission,
            variant,
            position,
        }: vir::Unfolding,
    ) -> Result<vir::Expr, Self::Error> {
        trace!(
            "[enter] fallible_fold_unfolding {}, {}, {}, {}",
            predicate,
            arguments[0],
            base,
            permission
        );

        let res = if self.wait_old_expr {
            vir::Expr::Unfolding(vir::Unfolding {
                predicate,
                arguments,
                base: self.fallible_fold_boxed(base)?,
                permission,
                variant,
                position,
            })
        } else {
            // Compute inner state
            let mut inner_pctxt = self.curr_pctxt.clone();
            let inner_state = inner_pctxt.mut_state();
            vir::Stmt::Unfold(vir::Unfold {
                predicate: predicate.clone(),
                arguments: arguments.clone(),
                permission,
                enum_variant: variant.clone(),
            })
            .apply_on_state(inner_state, self.curr_pctxt.predicates())?;

            // Store states
            let mut tmp_curr_pctxt = inner_pctxt;
            std::mem::swap(&mut self.curr_pctxt, &mut tmp_curr_pctxt);

            let inner_expr = self.fallible_fold_boxed(base)?;

            // Restore states
            std::mem::swap(&mut self.curr_pctxt, &mut tmp_curr_pctxt);

            vir::Expr::Unfolding(vir::Unfolding {
                predicate,
                arguments,
                base: inner_expr,
                permission,
                variant,
                position,
            })
        };

        trace!("[exit] fallible_fold_unfolding = {}", res);
        Ok(res)
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn fallible_fold_magic_wand(
        &mut self,
        vir::MagicWand {
            left,
            right,
            borrow,
            position,
        }: vir::MagicWand,
    ) -> Result<vir::Expr, Self::Error> {
        trace!("[enter] fallible_fold_magic_wand {}, {}", left, right);

        // Compute lhs state
        let mut lhs_pctxt = self.curr_pctxt.clone();
        let lhs_state = lhs_pctxt.mut_state();
        lhs_state.remove_all();
        lhs_state.insert_all_perms(
            left.get_footprint(self.curr_pctxt.predicates())
                .into_iter()
                .filter(|p| p.is_pred())
                .flat_map(|p| vec![Perm::acc(p.get_place().clone(), p.get_perm_amount()), p]),
        )?;
        lhs_state.replace_places(|place| {
            let pos = place.pos();
            place.old("lhs").set_pos(pos)
        });
        trace!("State of lhs of magic wand: {}", lhs_state);

        // Store states
        std::mem::swap(&mut self.curr_pctxt, &mut lhs_pctxt);

        // Rewrite lhs
        let new_lhs = self.fallible_fold_boxed(left)?;

        // Restore states
        std::mem::swap(&mut self.curr_pctxt, &mut lhs_pctxt);

        // Computer lhs state, now with unfoldings
        let mut new_lhs_pctxt = self.curr_pctxt.clone();
        let new_lhs_state = new_lhs_pctxt.mut_state();
        new_lhs_state.remove_all();
        new_lhs_state.insert_all_perms(
            new_lhs
                .get_footprint(self.curr_pctxt.predicates())
                .into_iter()
                .filter(|p| p.is_pred())
                .flat_map(|p| vec![Perm::acc(p.get_place().clone(), p.get_perm_amount()), p]),
        )?;
        new_lhs_state.replace_places(|place| {
            let pos = place.pos();
            place.old("lhs").set_pos(pos)
        });
        trace!("New state of lhs of magic wand: {}", new_lhs_state);

        // Compute rhs state
        let mut rhs_pctxt = self.curr_pctxt.clone();
        let rhs_state = rhs_pctxt.mut_state();
        rhs_state.remove_all();
        rhs_state.insert_all_perms(
            right
                .get_footprint(self.curr_pctxt.predicates())
                .into_iter()
                .filter(|p| p.is_pred())
                .flat_map(|p| vec![Perm::acc(p.get_place().clone(), p.get_perm_amount()), p]),
        )?;
        trace!("State of rhs of magic wand: {}", rhs_state);

        // Store states
        std::mem::swap(&mut self.curr_pctxt, &mut rhs_pctxt);
        self.lhs_pctxt = Some(new_lhs_pctxt);

        // Rewrite rhs
        let new_rhs = self.fallible_fold_boxed(right)?;

        // Restore states
        self.lhs_pctxt = None;
        std::mem::swap(&mut self.curr_pctxt, &mut rhs_pctxt);

        // Rewrite lhs and build magic wand
        let res = vir::Expr::MagicWand(vir::MagicWand {
            left: new_lhs,
            right: new_rhs,
            borrow,
            position,
        });

        trace!("[enter] fallible_fold_magic_wand = {}", res);
        Ok(res)
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn fallible_fold_labelled_old(
        &mut self,
        vir::LabelledOld {
            label,
            base,
            position,
        }: vir::LabelledOld,
    ) -> Result<vir::Expr, Self::Error> {
        trace!("[enter] fallible_fold_labelled_old {}: {}", label, base);

        let mut tmp_curr_pctxt = if label == "lhs" && self.lhs_pctxt.is_some() {
            self.lhs_pctxt.as_ref().unwrap().clone()
        } else {
            self.pctxt_at_label
                .get(&label)
                .map_or_else(|| Err(FoldUnfoldError::MissingLabel(label.clone())), Ok)?
                .clone()
        };

        // Replace old[label] with curr
        tmp_curr_pctxt.mut_state().replace_places(|place| {
            place.map_labels(|opt_label| {
                if opt_label == label.clone() {
                    None
                } else {
                    Some(opt_label)
                }
            })
        });

        // Store states
        std::mem::swap(&mut self.curr_pctxt, &mut tmp_curr_pctxt);
        let old_wait_old_expr = self.wait_old_expr;
        self.wait_old_expr = false;

        // Rewrite inner expression
        let inner_expr = self.fallible_fold_boxed(base)?;

        // Restore states
        std::mem::swap(&mut self.curr_pctxt, &mut tmp_curr_pctxt);
        self.wait_old_expr = old_wait_old_expr;

        // Rebuild expression
        let res = vir::Expr::LabelledOld(vir::LabelledOld {
            label,
            base: inner_expr,
            position,
        });

        trace!("[exit] fallible_fold_labelled_old = {}", res);
        Ok(res)
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn fallible_fold_downcast(
        &mut self,
        vir::DowncastExpr {
            base,
            enum_place,
            field,
        }: vir::DowncastExpr,
    ) -> Result<vir::Expr, Self::Error> {
        trace!(
            "[enter] fallible_fold_downcast {} -> {} in {}",
            enum_place,
            field,
            base
        );

        let res = if self.wait_old_expr {
            vir::Expr::Downcast(vir::DowncastExpr {
                base: self.fallible_fold_boxed(base)?,
                enum_place,
                field,
            })
        } else {
            // Compute inner state
            let mut inner_pctxt = self.curr_pctxt.clone();
            let inner_state = inner_pctxt.mut_state();
            vir::Stmt::Downcast(vir::Downcast {
                base: enum_place.as_ref().clone(),
                field: field.clone(),
            })
            .apply_on_state(inner_state, self.curr_pctxt.predicates())?;

            // Store states
            let mut tmp_curr_pctxt = inner_pctxt;
            std::mem::swap(&mut self.curr_pctxt, &mut tmp_curr_pctxt);

            let inner_base = self.fallible_fold_boxed(base)?;

            // Restore states
            std::mem::swap(&mut self.curr_pctxt, &mut tmp_curr_pctxt);

            vir::Expr::Downcast(vir::DowncastExpr {
                base: inner_base,
                enum_place,
                field,
            })
        };

        trace!("[exit] fallible_fold_downcast = {}", res);
        Ok(res)
    }

    fn fallible_fold_forall(&mut self, expr: vir::ForAll) -> Result<vir::Expr, Self::Error> {
        let vir::ForAll {
            variables,
            triggers,
            body,
            position,
        } = expr;
        Ok(vir::Expr::ForAll(vir::ForAll {
            variables,
            // triggers should be skipped
            triggers,
            body: self.fallible_fold_boxed(body)?,
            position,
        }))
    }

    fn fallible_fold_exists(&mut self, expr: vir::Exists) -> Result<vir::Expr, Self::Error> {
        let vir::Exists {
            variables,
            triggers,
            body,
            position,
        } = expr;
        Ok(vir::Expr::Exists(vir::Exists {
            variables,
            // triggers should be skipped
            triggers,
            body: self.fallible_fold_boxed(body)?,
            position,
        }))
    }
}
