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

    // pub fn new_tree_permissions_state(&self, loop_head: BasicBlockIndex) -> TreePermissionEncodingState<'_, 'tcx> {
    //     unimplemented!()
    // }
}

pub struct TreePermissionEncodingState<'tcx> {
    loop_head: BasicBlockIndex,
    non_quantified: Vec<vir::PlainResourceAccess>,
    quantified: Vec<Vec<vir::PlainResourceAccess>>,
    quantified_vars: Vec<vir::LocalVar>,
    subst: HashMap<vir::Expr, vir::Expr>,
    preconds_and_triggers: HashMap<vir::LocalVar, (vir::Expr, Vec<vir::Trigger>)>,
    seen_places: HashSet<mir::Place<'tcx>>,
    seen_permissions: HashSet<vir::PlainResourceAccess>,
    uninits: HashSet<vir::Expr>,
    counter: usize,
}

impl<'tcx> TreePermissionEncodingState<'tcx> {
    pub fn new(loop_head: BasicBlockIndex) -> Self {
        TreePermissionEncodingState {
            loop_head,
            non_quantified: Vec::new(),
            quantified: Vec::new(),
            quantified_vars: Vec::new(),
            subst: HashMap::new(),
            preconds_and_triggers: HashMap::new(),
            seen_places: HashSet::new(),
            seen_permissions: HashSet::new(),
            uninits: HashSet::new(),
            counter: 0,
        }
    }

    pub fn encode_place<'slf>(
        &mut self,
        encoder: &'slf Encoder<'_, '_, '_, 'tcx>,
        mir_encoder: &'slf MirEncoder<'_, '_, '_, '_, 'tcx>,
        loop_encoder: &'slf LoopEncoder<'_, 'tcx>,
        place: &mir::Place<'tcx>,
    ) -> (vir::Expr, ty::Ty<'tcx>, Option<usize>) {
        if let Some((array, index)) = Self::indexing_suffix(place) {
            // TODO: insert index place and not the whole place
            //  Also rename "seen_places" to something else
            let is_new = self.seen_places.insert(place.clone());
            let is_init = || loop_encoder.is_definitely_initialised(&mir::Place::Local(index), self.loop_head);
            if is_new && !is_init() {
                // TODO: can we be certain that the index translated alone will
                //  be the same when it is translated with the array indexing?
                //  (ditto for array)
                let (encoded_array, array_ty, _) = mir_encoder.encode_place(array);
                info!("AAA {:?}", array_ty);
                let encoded_array = encoded_array.field(
                    TypeEncoder::new(encoder, array_ty)
                        .encode_value_field()
                );
                info!("BBB {}", encoded_array);
                let encoded_index = vir::Expr::local(mir_encoder.encode_local(index))
                    .field(TypeEncoder::new(encoder, mir_encoder.get_local_ty(index)).encode_value_field());
                // self.uninits.insert(vir::Expr::local(encoded_index.clone()));
                self.uninits.insert(encoded_index.clone());
                let quantified_index = self.fresh_index_local_var();
                let quantified_index_expr = vir::Expr::local(quantified_index.clone());

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
                let trigger = vir::Trigger::new(vec![vir::Expr::seq_index(encoded_array, quantified_index_expr.clone())]);
                self.preconds_and_triggers.insert(
                    quantified_index.clone(),
                    (precondition, vec![trigger])
                );
                info!("CCC {}", encoded_index);
                // self.subst.insert(vir::Expr::local(encoded_index), quantified_index_expr);
                self.subst.insert(encoded_index, quantified_index_expr);
                self.quantified.push(Vec::new());
                self.quantified_vars.push(quantified_index);
            }
        }
        let (encoded_place, ty, variant) = mir_encoder.encode_place(place);
        info!("DDDD {}", encoded_place);
        let other = self.subst.iter().fold(encoded_place.clone(), |expr, (a, b)| expr.replace_place(a, b));
        info!("EEEE {}", other);
        (encoded_place.subst(&self.subst), ty, variant)
    }

    pub fn add(&mut self, access: vir::PlainResourceAccess) {
        if !self.seen_permissions.insert(access.clone()) {
            return;
        }
        match access.get_place() {
            vir::Expr::SeqIndex(box ref seq, box ref index, _)
          | vir::Expr::Field(box vir::Expr::SeqIndex(box ref seq, box ref index, _), _, _) => {
                if !self.uninits.contains(index) && index.is_place() { // TODO: is is_place ok?
                    // TODO
                    // self.add(vir::ResourceAccess::field(index.clone(), vir::PermAmount::Read));
                }
                self.add(vir::PlainResourceAccess::field(seq.clone(), access.get_perm_amount()));
            }
            _ => (),
        }
        info!("PUSHING {}", access);
        if self.subst.is_empty() {
            self.non_quantified.push(access);
        } else {
            self.quantified.last_mut().expect("Cannot be None")
                .push(access);
        }
    }

    // TODO: flatten forall and return vec of vir::ResourceAccess
    pub fn get_permissions(mut self) -> Vec<vir::Expr> {
        let mut result = Vec::new();
        result.extend(self.non_quantified.into_iter().map(|access| access.into()));
        assert_eq!(self.quantified.len(), self.quantified_vars.len());

        let mut previous_forall_level: Option<vir::Expr> = None;
        for (var, accesses) in self.quantified_vars.into_iter().rev().zip(self.quantified.into_iter().rev()) {
            let (_, (precond, triggers)) = self.preconds_and_triggers.remove_entry(&var)
                .expect("Cannot be None");
            let conjunct = accesses.into_iter().map(|access| access.into()).conjoin();
            let forall_body = match previous_forall_level.take() {
                Some(previous_level) => vir::Expr::and(conjunct, previous_level),
                None => conjunct
            };
            let forall_expr = vir::Expr::forall(vec![var], triggers, vir::Expr::implies(precond, forall_body));
            previous_forall_level = Some(forall_expr);
        }

        if let Some(foralls) = previous_forall_level.take() {
            result.push(foralls);
        }

        result
    }

    fn fresh_index_local_var(&mut self) -> vir::LocalVar {
        let result = vir::LocalVar::new(format!("__i_{}", self.counter), vir::Type::Int);
        self.counter += 1;
        result
    }

    fn indexing_suffix<'a>(place: &'a mir::Place<'tcx>) -> Option<(&'a mir::Place<'tcx>, mir::Local)>
        where 'tcx: 'a
    {
        match place {
            mir::Place::Projection(box mir::Projection {
                ref base,
                elem: mir::ProjectionElem::Index(index),
            }) => Some((base, *index)),
            _ => None
        }
    }
}