// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_interface::utils;
use prusti_interface::environment::{
    BasicBlockIndex, PlaceAccess, PlaceAccessKind, ProcedureLoops, PermissionForest};
use rustc::mir;
use rustc::ty;
use std::collections::HashMap;
use prusti_interface::environment::mir_analyses::initialization::{
    compute_definitely_initialized,
    DefinitelyInitializedAnalysisResult
};
use rustc::hir::def_id::DefId;
use prusti_interface::environment::place_set::PlaceSet;

pub struct LoopEncoder<'a, 'tcx: 'a> {
    mir: &'a mir::Mir<'tcx>,
    tcx: ty::TyCtxt<'a, 'tcx, 'tcx>,
    loops: ProcedureLoops,
    initialization: DefinitelyInitializedAnalysisResult<'tcx>,
}

impl<'a, 'tcx: 'a> LoopEncoder<'a, 'tcx> {

    pub fn new(mir: &'a mir::Mir<'tcx>, tcx: ty::TyCtxt<'a, 'tcx, 'tcx>, def_id: DefId) -> LoopEncoder<'a, 'tcx>
    {
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
        self.get_loop_head(bbi).map(
            |head| self.loops.get_loop_head_depth(head)
        ).unwrap_or(0)
    }

    pub fn compute_loop_invariant(&self, bb: BasicBlockIndex) -> PermissionForest<'tcx>
    {
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
        let (write_leaves, read_leaves) = self.loops.compute_read_and_write_leaves(
            bb, self.mir, None);

        let mut all_places = PlaceSet::new();
        for place in &read_leaves {
            all_places.insert(&place, self.mir, self.tcx)
        }
        for place in &write_leaves {
            all_places.insert(&place, self.mir, self.tcx)
        }

        // Construct the permission forest.
        let forest = PermissionForest::new(&write_leaves, &read_leaves, &all_places);

        forest
    }
}
