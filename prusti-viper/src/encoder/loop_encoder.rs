// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_interface::environment::mir_analyses::initialization::{
    compute_definitely_initialized, DefinitelyInitializedAnalysisResult,
};
use prusti_interface::environment::place_set::PlaceSet;
use prusti_interface::environment::{
    BasicBlockIndex, PermissionForest, ProcedureLoops,
};
use prusti_interface::utils;
use rustc::hir::def_id::DefId;
use rustc::mir;
use rustc::ty;
use encoder::{vir, Encoder};
use std::collections::{HashMap, HashSet};
use std::collections::hash_map::Entry;
use std::iter::Peekable;
use encoder::type_encoder::TypeEncoder;
use encoder::vir::ExprIterator;
use encoder::mir_encoder::MirEncoder;

pub struct LoopEncoder<'a, 'tcx: 'a> {
    mir: &'a mir::Mir<'tcx>,
    tcx: ty::TyCtxt<'a, 'tcx, 'tcx>,
    loops: ProcedureLoops,
    initialization: DefinitelyInitializedAnalysisResult<'tcx>,
}

impl<'a, 'tcx: 'a> LoopEncoder<'a, 'tcx> {
    pub fn new(
        mir: &'a mir::Mir<'tcx>,
        tcx: ty::TyCtxt<'a, 'tcx, 'tcx>,
        def_id: DefId,
    ) -> LoopEncoder<'a, 'tcx> {
        let def_path = tcx.hir.def_path(def_id);
        LoopEncoder {
            mir,
            tcx,
            loops: ProcedureLoops::new(mir),
            initialization: compute_definitely_initialized(&mir, tcx, def_path),
        }
    }

    /// Is the given basic block a loop head?
    pub fn is_loop_head(&self, bbi: BasicBlockIndex) -> bool {
        self.loops.is_loop_head(bbi)
    }

    /// Note: a loop head is loop head of itself
    pub fn get_loop_head(&self, bbi: BasicBlockIndex) -> Option<BasicBlockIndex> {
        self.loops.get_loop_head(bbi)
    }

    /// 0 = outside loops, 1 = inside one loop, 2 = inside 2 loops and so on
    pub fn get_loop_depth(&self, bbi: BasicBlockIndex) -> usize {
        self.get_loop_head(bbi)
            .map(|head| self.loops.get_loop_head_depth(head))
            .unwrap_or(0)
    }

    /// Get iterator over enclosing loop heads.
    pub fn get_enclosing_loop_heads(&self, bbi: BasicBlockIndex) -> Vec<BasicBlockIndex> {
        self.loops.get_enclosing_loop_heads(bbi)
    }

    pub fn compute_loop_invariant(&self, bb: BasicBlockIndex) -> PermissionForest<'tcx> {
        assert!(self.is_loop_head(bb));

        // 1.  Let ``A1`` be a set of pairs ``(p, t)`` where ``p`` is a prefix
        //     accessed in the loop body and ``t`` is the type of access (read,
        //     destructive read, …).
        // 2.  Let ``A2`` be a subset of ``A1`` that contains only the prefixes
        //     whose roots are defined before the loop. (The root of the prefix
        //     ``x.f.g.h`` is ``x``.)
        // 3.  Let ``A3`` be a subset of ``A2`` without accesses that are subsumed
        //     by other accesses.
        // 4.  Let ``U`` be a set of prefixes that are unreachable at the loop
        //     head because they are either moved out or mutably borrowed.
        // 5.  For each access ``(p, t)`` in the set ``A3``:
        //
        //     1.  Add a read permission to the loop invariant to read the prefix
        //         up to the last element. If needed, unfold the corresponding
        //         predicates.
        //     2.  Add a permission to the last element based on what is required
        //         by the type of access. If ``p`` is a prefix of some prefixes in
        //         ``U``, then the invariant would contain corresponding predicate
        //         bodies without unreachable elements instead of predicates.

        // Paths accessed inside the loop body.
        let (write_leaves, mut_borrow_leaves, read_leaves) =
            self.loops.compute_read_and_write_leaves(
                bb,
                self.mir,
                Some(self.initialization.get_before_block(bb)),
            );

        let mut all_places = PlaceSet::new();
        for place in &read_leaves {
            all_places.insert(&place, self.mir, self.tcx)
        }
        for place in &mut_borrow_leaves {
            all_places.insert(&place, self.mir, self.tcx)
        }
        for place in &write_leaves {
            all_places.insert(&place, self.mir, self.tcx)
        }

        // Construct the permission forest.
        let forest =
            PermissionForest::new(&write_leaves, &mut_borrow_leaves, &read_leaves, &all_places);

        forest
    }

    /// Is the ``place`` definitely initialised at the beginning of ``bbi``?
    pub fn is_definitely_initialised(&self, place: &mir::Place, bbi: BasicBlockIndex) -> bool {
        self.initialization
            .get_before_block(bbi)
            .iter()
            .any(|def_init_place| utils::is_prefix(place, def_init_place))
    }
}

pub struct TreePermissionEncodingState {
    loop_head: BasicBlockIndex,
    uninits: HashSet<vir::Expr>,
    subst: HashMap<vir::Expr, vir::Expr>,
    quantification: HashMap<vir::LocalVar, (Vec<vir::Trigger>, vir::Expr)>,
    permissions: HashSet<vir::PlainResourceAccess>,
    counter: usize,
}

impl TreePermissionEncodingState {
    pub fn new(loop_head: BasicBlockIndex) -> Self {
        TreePermissionEncodingState {
            loop_head,
            uninits: HashSet::new(),
            subst: HashMap::new(),
            quantification: HashMap::new(),
            permissions: HashSet::new(),
            counter: 0,
        }
    }

    pub fn encode_place<'slf, 'tcx: 'slf>(
        &mut self,
        mir_encoder: &'slf MirEncoder<'_, '_, '_, '_, 'tcx>,
        loop_encoder: &'slf LoopEncoder<'_, 'tcx>,
        place: &mir::Place<'tcx>,
    ) -> (vir::Expr, ty::Ty<'tcx>, Option<usize>) {
        let (encoded_place, ty, variant) = mir_encoder.encode_place(place);
        if let Some((array, index)) = Self::indexing_suffix(place) {
            let (encoded_array, encoded_index) =
                Self::extract_seq_and_index(&encoded_place)
                    .expect("MIR indexing got converted to something else than SeqIndex");
            if !self.uninits.contains(&encoded_index) &&
                !loop_encoder.is_definitely_initialised(&mir::Place::Local(index), self.loop_head) {
                // Add the index to the uninitialized variables so that we don't repeat the process
                // again if we see it again it the future.
                self.uninits.insert(encoded_index.clone());
                // Creating a fresh quantified index
                let quantified_index = self.fresh_index_local_var();
                let quantified_index_expr = vir::Expr::local(quantified_index.clone());

                // Creating the trigger and the precondition
                let trigger = vir::Trigger::new(vec![
                    vir::Expr::seq_index(encoded_array.clone(), quantified_index_expr.clone())
                ]);
                // 0 <= i && i < |array|
                let precondition = vir::Expr::and(
                    vir::Expr::le_cmp(
                        vir::Expr::Const(vir::Const::Int(0), vir::Position::default()),
                        quantified_index_expr.clone()
                    ),
                    vir::Expr::lt_cmp(
                        quantified_index_expr.clone(),
                        vir::Expr::seq_len(encoded_array.clone())
                    )
                );
                self.quantification.insert(quantified_index, (vec![trigger], precondition));

                // Adding the substitution.
                // Instead of referring to the uninit. index,
                // expressions will refer to the new quantified index.
                self.subst.insert(encoded_index.clone(), quantified_index_expr);
            }
        }
        info!("DDDD {}", encoded_place);
        let other = self.subst.iter().fold(encoded_place.clone(), |expr, (a, b)| expr.replace_place(a, b));
        info!("EEEE {}", other);
        (encoded_place.subst(&self.subst), ty, variant)
    }

    pub fn add(&mut self, access: vir::PlainResourceAccess) {
        if !self.permissions.insert(access.clone()) {
            return;
        }
        if let Some((seq, index)) = Self::extract_seq_and_index(access.get_place()) {
            // If the index is free (i.e., not a quantified var), we require a field access
            if self.is_variable_free(index) && index.is_place() {
                self.add(vir::PlainResourceAccess::field(index.clone(), vir::PermAmount::Read));
            }
            self.add(vir::PlainResourceAccess::field(seq.clone(), access.get_perm_amount()));
        }

        info!("PUSHING {}", access);
        self.permissions.insert(access);
    }

    pub fn get_permissions(self) -> Vec<vir::Expr> {
        let quantification = self.quantification;
        let mut result = self.permissions.into_iter().map(|resource| {
            let quant_vars = quantification.keys()
                .filter(|&var| resource.get_place().find(&vir::Expr::local(var.clone())))
                .collect::<HashSet<_>>();
            if quant_vars.is_empty() {
                vir::ResourceAccess::Plain(resource).into()
            } else {
                let (triggers, conds): (Vec<_>, Vec<_>) = quantification.iter()
                    .filter(|(var, _)| quant_vars.contains(var))
                    .map(|(_, (triggers, cond))| (triggers.clone(), cond.clone()))
                    .unzip();
                vir::ResourceAccess::Quantified(vir::QuantifiedResourceAccess {
                    vars: quant_vars.into_iter().cloned().collect(),
                    triggers: triggers.into_iter().flat_map(|x| x.into_iter()).collect(),
                    cond: box Self::conjoin_no_trailing_true(conds),
                    resource
                }).into()
            }
        }).collect::<Vec<_>>();
        Self::simple_sort_by_prefix(&mut result);
        info!("[exit] get_permissions permissions=\n{}",
              result
                .iter()
                .map(|p| format!("\t{}", p))
                .collect::<Vec<String>>()
                .join("\n")
        );
        result
    }

    fn fresh_index_local_var(&mut self) -> vir::LocalVar {
        let result = vir::LocalVar::new(format!("__i_{}", self.counter), vir::Type::Int);
        self.counter += 1;
        result
    }

    fn is_variable_free(&self, index: &vir::Expr) -> bool {
        match index {
            vir::Expr::Local(lv, _) => !self.quantification.contains_key(lv),
            _ => true,
        }
    }

    fn extract_seq_and_index(expr: &vir::Expr) -> Option<(&vir::Expr, &vir::Expr)> {
        match expr {
            vir::Expr::SeqIndex(box ref seq, box ref index, _)
            | vir::Expr::Field(box vir::Expr::SeqIndex(box ref seq, box ref index, _), _, _) =>
                Some((seq, index)),
            _ => None
        }
    }

    fn indexing_suffix<'a, 'tcx: 'a>(
        place: &'a mir::Place<'tcx>
    ) -> Option<(&'a mir::Place<'tcx>, mir::Local)> {
        match place {
            mir::Place::Projection(box mir::Projection {
                ref base,
                elem: mir::ProjectionElem::Index(index),
            }) => Some((base, *index)),
            _ => None
        }
    }

    fn simple_sort_by_prefix(exprs: &mut Vec<vir::Expr>) {
        fn has_proper_prefix_resource_access(lhs: &vir::Expr, rhs: &vir::Expr) -> bool {
            if lhs.is_place() && rhs.is_place() {
                return lhs.has_proper_prefix(rhs);
            }
            match (lhs, rhs) {
                (
                    vir::Expr::FieldAccessPredicate(lhs, _, _),
                    vir::Expr::FieldAccessPredicate(rhs, _, _),
                ) => lhs.has_proper_prefix(rhs),
                (
                    vir::Expr::PredicateAccessPredicate(_, lhs, _, _),
                    vir::Expr::PredicateAccessPredicate(_, rhs, _, _),
                ) => lhs.has_proper_prefix(rhs),
                (
                    vir::Expr::PredicateAccessPredicate(_, lhs, _, _),
                    vir::Expr::FieldAccessPredicate(rhs, _, _),
                ) => lhs.has_prefix(rhs),
                (
                    vir::Expr::QuantifiedResourceAccess(lhs, _),
                    vir::Expr::QuantifiedResourceAccess(rhs, _)
                ) =>
                    lhs.cond == rhs.cond &&
                        // We recurse so that we don't duplicate the handling of FAP or PAP
                        has_proper_prefix_resource_access(
                            &lhs.resource.to_expression(),
                            &rhs.resource.to_expression()
                        ),
                (
                    vir::Expr::QuantifiedResourceAccess(lhs, _),
                    vir::Expr::FieldAccessPredicate(rhs, _, _)
                ) => lhs.resource.get_place().has_prefix(rhs),
                (
                    vir::Expr::QuantifiedResourceAccess(lhs, _),
                    vir::Expr::PredicateAccessPredicate(_, rhs, _, _)
                ) => lhs.resource.get_place().has_prefix(rhs),
                _ => false,
            }
        }

        fn suffixes_of<'a>(exprs: &'a Vec<vir::Expr>, expr: &'a vir::Expr) -> impl Iterator<Item=usize> + 'a {
            exprs.iter().enumerate()
                .filter(move |(_, e)| has_proper_prefix_resource_access(expr, e))
                .map(|(index, _)| index)
        }

        fn topo_sort(
            exprs: &Vec<vir::Expr>,
            visited: &mut Vec<bool>,
            topo_sorted: &mut Vec<vir::Expr>,
            curr_index: usize
        ) {
            assert!(!visited[curr_index]);
            visited[curr_index] = true;
            let curr_expr = &exprs[curr_index];
            for index in suffixes_of(exprs, curr_expr) {
                if !visited[index] {
                    topo_sort(exprs, visited, topo_sorted, index);
                }
            }
            topo_sorted.push(exprs[curr_index].clone())
        }

        let mut visited: Vec<bool> = vec![false; exprs.len()];
        let mut topo_sorted: Vec<vir::Expr> = vec![];
        for index in 0..exprs.len() {
            if !visited[index] {
                topo_sort(exprs, &mut visited, &mut topo_sorted, index);
            }
        }

        *exprs = topo_sorted;
    }

    // Like vir::Expr::conjoin, but without the trailing `&& true` that causes issue with
    // QuantifiedResourceAccess and its is_similar method
    fn conjoin_no_trailing_true(exprs: Vec<vir::Expr>) -> vir::Expr {
        fn rfold<T>(mut s: Peekable<T>) -> vir::Expr
            where T: Iterator<Item = vir::Expr>
        {
            match (s.next(), s.peek()) {
                (Some(e1), Some(_)) =>
                    vir::Expr::and(e1, rfold(s)),
                (Some(e), None) =>
                    e,
                _ => unreachable!()
            }
        }
        if exprs.is_empty() {
            true.into()
        } else {
            rfold(exprs.into_iter().peekable())
        }
    }
}