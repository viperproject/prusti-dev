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
use encoder::vir;
use std::collections::HashSet;

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
    permissions: HashSet<vir::PlainResourceAccess>,
}

impl TreePermissionEncodingState {
    pub fn new() -> Self {
        TreePermissionEncodingState {
            permissions: HashSet::new(),
        }
    }

    pub fn add(&mut self, access: vir::PlainResourceAccess) {
        if let Some((seq, _)) = access.get_place().extract_seq_and_index() {
            match seq {
                vir::Expr::Field(seq_re, field, _) if field.name == "val_array" && field.typ.get_id() == vir::TypeId::Seq => {
                    self.add(
                        vir::PlainResourceAccess::predicate(
                            *seq_re.clone(),
                            access.get_perm_amount()
                        ).unwrap()
                    );
                    // Do not add the indexing itself (e.g. _1.val_ref.val_array[idx])
                    // into the permissions. It will be handled by the undfolding of the
                    // array predicate.
                    return;
                }
                x => unreachable!("{}", x),
            }
        }

        info!("PUSHING {}", access);
        self.permissions.insert(access);
    }

    pub fn get_permissions(self) -> Vec<vir::Expr> {
        let mut result = self.permissions.into_iter().map(|r| r.into()).collect::<Vec<_>>();
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

        fn suffixes_of<'a>(
            exprs: &'a Vec<vir::Expr>,
            expr: &'a vir::Expr
        ) -> impl Iterator<Item=usize> + 'a {
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
}