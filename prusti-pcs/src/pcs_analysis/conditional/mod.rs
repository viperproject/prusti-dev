// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
#![allow(unused_imports)]
use crate::{
    graph::{ReborrowingGraph::*, *},
    joins::{RepackPackup, RepackUnify},
    syntax::{
        hoare_semantics::HoareSemantics, LinearResource, MicroMirData, MicroMirEncoder,
        MicroMirEncoding, MicroMirStatement, MicroMirTerminator, PCSPermission, PCSPermissionKind,
        PCSPermissionKind::*, PCS,
    },
    util::EncodingResult,
};
use analysis::mir_utils::expand_struct_place;
use prusti_interface::{
    environment::{
        mir_analyses::{
            allocation::DefinitelyAllocatedAnalysisResult,
            initialization::DefinitelyInitializedAnalysisResult,
        },
        mir_sets::{LocalSet, PlaceSet},
        polonius_info::PoloniusInfo,
        Environment,
    },
    utils::is_prefix,
    PrustiError,
};
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    errors::MultiSpan,
    middle::mir::{BasicBlock, Body, Location, Mutability, Mutability::*, Place},
};
use std::{
    cmp::min,
    iter::{repeat, zip},
};

/// Straight line, fully elaborated MicroMir
/// INVARIANT: coherent pre- and post- conditions
/// INVARIANT: len(statements) == len(pcs_before)
/// todo: remove the pub(crate) permission here... implement iterator.
pub struct StraightOperationalMir<'tcx> {
    statements: Vec<MicroMirStatement<'tcx>>,
    pcs_before: Vec<PCS<'tcx>>,
}

impl<'tcx> StraightOperationalMir<'tcx> {
    pub fn len(&self) -> usize {
        min(self.statements.len(), self.pcs_before.len())
    }

    pub fn get(&self, index: usize) -> (&PCS<'tcx>, &MicroMirStatement<'tcx>) {
        (&self.pcs_before[index], &self.statements[index])
    }
}

pub struct StraightOperationalMirIter<'a, 'tcx: 'a> {
    base: &'a StraightOperationalMir<'tcx>,
    index: usize,
}

impl<'a, 'tcx: 'a> IntoIterator for &'a StraightOperationalMir<'tcx> {
    type Item = (&'a PCS<'tcx>, &'a MicroMirStatement<'tcx>);
    type IntoIter = StraightOperationalMirIter<'a, 'tcx>;

    fn into_iter(self) -> Self::IntoIter {
        StraightOperationalMirIter {
            base: self,
            index: 0,
        }
    }
}

impl<'a, 'tcx: 'a> Iterator for StraightOperationalMirIter<'a, 'tcx> {
    type Item = (&'a PCS<'tcx>, &'a MicroMirStatement<'tcx>);
    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.base.len() {
            let ret = self.base.get(self.index);
            self.index += 1;
            Some(ret)
        } else {
            None
        }
    }
}

impl<'tcx> Default for StraightOperationalMir<'tcx> {
    fn default() -> StraightOperationalMir<'tcx> {
        StraightOperationalMir {
            statements: vec![],
            pcs_before: vec![],
        }
    }
}

/// OperationalMIR which lives on CFG edges,
/// Does not correspond to any MIR location
pub struct PostBlock<'tcx> {
    pub body: StraightOperationalMir<'tcx>,
    pub next: BasicBlock,
}

/// Result of a CondPCS procedure
pub struct CondPCSBlock<'tcx> {
    body: StraightOperationalMir<'tcx>,
    terminator_precondition: PCS<'tcx>,
    terminator: MicroMirTerminator<'tcx>,
    pcs_after: Vec<(PostBlock<'tcx>, PCS<'tcx>)>,
}

/// Result of a CondPCS procedure
pub struct CondPCS<'tcx> {
    pub blocks: FxHashMap<BasicBlock, CondPCSBlock<'tcx>>,
}

impl<'tcx> CondPCS<'tcx> {
    pub fn pprint(&self) {
        for (current_bb, cond_pcs_block) in self.blocks.iter() {
            println!(
                " ===================== {:?} ===================== ",
                current_bb
            );

            for (pcs, st) in (&(cond_pcs_block.body)).into_iter() {
                print!("\tPCS: ");
                pcs.pprint_contents();
                println!();
                println!("\t\t{:?}", st);
            }

            print!("\tPCS: ");
            cond_pcs_block.terminator_precondition.pprint_contents();
            println!();

            println!("\t\t{:?}", cond_pcs_block.terminator);

            for (post_block, post_pcs) in cond_pcs_block.pcs_after.iter() {
                println!("\t~ {:?} ~>", post_block.next);
                for (pcs, st) in (&(post_block.body)).into_iter() {
                    print!("\t\tPCS: ");
                    pcs.pprint_contents();
                    println!();
                    println!("\t\t\t{:?}", st);
                }
                println!("\t\t~> {:?}", post_pcs);
            }

            println!();
        }
        println!();
    }
}

/// Collection of all information needed to compute the CondPCS
/// statically computed beforehand (input facts)
pub struct CondPCSctx<'mir, 'env: 'mir, 'tcx: 'env> {
    pub micro_mir: &'mir MicroMirEncoding<'tcx>,
    pub mir: &'mir Body<'tcx>,
    pub env: &'env Environment<'tcx>,
    pub init_analysis: DefinitelyInitializedAnalysisResult<'tcx>,
    pub alloc_analysis: DefinitelyAllocatedAnalysisResult,
    pub polonius_info: PoloniusInfo<'mir, 'tcx>,
}

/// Data structure for all computations of the CondPCS
impl<'mir, 'env: 'mir, 'tcx: 'env> CondPCSctx<'mir, 'env, 'tcx> {
    pub fn cond_pcs(&self) -> EncodingResult<CondPCS<'tcx>> {
        // Map of blocks and their Operational PCS's
        let mut generated_blocks: FxHashMap<BasicBlock, CondPCSBlock<'tcx>> = FxHashMap::default();

        // Computation left to do
        let mut dirty_blocks = self.initial_state();

        while let Some((bb, mut pcs)) = dirty_blocks.pop() {
            // Translate the basic block bb, starting with PCS pcs
            //  (this should be the exact PCS that all in-edges end up with)
            let block_data = self.get_block_data(&bb)?;
            let mut body = StraightOperationalMir::default();
            pcs = self.translate_body(block_data, &mut body, pcs)?;

            // Repack to apply the terminaor PCS
            let terminator = &block_data.terminator;
            pcs = self.repack(pcs, &terminator.precondition(), &mut body)?;

            let terminator_precondition = pcs.clone();

            let mut pcs_after: Vec<(PostBlock<'tcx>, PCS<'tcx>)> = Vec::default();

            for (next_block, dependent_postcondition) in terminator.postcondition() {
                //      Apply the semantics (we are now joinable mod repacks)
                let mut this_pcs = transform_pcs(
                    pcs.clone(),
                    &terminator.precondition(),
                    &dependent_postcondition,
                )?;

                let mut this_op_mir = StraightOperationalMir::default();

                // Trim the PCS by way of eager drops (we are now the same mod repacks)
                this_pcs = self.trim_pcs(next_block, &mut this_pcs, &mut this_op_mir)?;

                // Pack to the most packed state possible (we are now identical)
                // (any unique state works)
                this_pcs = self.packup(this_pcs, &mut this_op_mir)?;

                // If the next block is not already done, add it as a dirty block (to do)
                if let Some(done_block) = generated_blocks.get(&next_block) {
                    // Check that the final PCS is the same as the
                    // intial PCS in the block
                    if this_pcs != done_block.body.pcs_before[0] {
                        println!("init {:?}", self.init_analysis.get_before_block(next_block));

                        println!(
                            "alloc {:?}",
                            self.alloc_analysis.get_before_block(next_block)
                        );
                        return Err(PrustiError::internal(
                            format!("trimmed+packed pcs ({:?}) does not match existing block ({:?}) exiting a join", this_pcs, done_block.body.pcs_before[0]),
                            MultiSpan::new(),
                        ));
                    }
                } else if let Some(todo_pcs) = dirty_blocks
                    .iter()
                    .filter_map(|(todo_bb, todo_pcs)| {
                        if *todo_bb == next_block {
                            Some(todo_pcs)
                        } else {
                            None
                        }
                    })
                    .next()
                {
                    // Check that the final PCS is the same as the
                    // intial PCS in the block
                    if this_pcs != *todo_pcs {
                        return Err(PrustiError::internal(
                            "trimmed+packed pcs does not join with a dirty PCS",
                            MultiSpan::new(),
                        ));
                    }
                } else {
                    // Mark the next block as dirty
                    dirty_blocks.push((next_block, this_pcs.clone()));
                }

                pcs_after.push((
                    PostBlock {
                        body: this_op_mir,
                        next: next_block,
                    },
                    this_pcs,
                ));
            }

            generated_blocks.insert(
                block_data.mir_block,
                CondPCSBlock {
                    body,
                    terminator_precondition,
                    terminator: (*terminator).clone(),
                    pcs_after,
                },
            );
        }

        Ok(CondPCS {
            blocks: generated_blocks,
        })
    }

    // Straight-line PCS computation inside the body of a basic block
    fn translate_body(
        &self,
        block_data: &MicroMirData<'tcx>,
        op_mir: &mut StraightOperationalMir<'tcx>,
        mut pcs: PCS<'tcx>,
    ) -> EncodingResult<PCS<'tcx>> {
        // Dumb hack: For each MIR parent, find the last index
        let it = block_data.statements.iter().enumerate().map(|(i, _)| i);
        let it1 = block_data
            .statements
            .iter()
            .enumerate()
            .map(|(i, _)| i)
            .skip(1);

        let mut polonius_apply_places: Vec<usize> = vec![];
        for (st, next) in zip(it, it1) {
            if block_data.mir_parent[st] != block_data.mir_parent[next] {
                polonius_apply_places.push(next);
            }
        }

        for (statement_index, statement) in block_data.statements.iter().enumerate() {
            let location = Location {
                block: block_data.mir_block,
                statement_index: block_data.mir_parent[statement_index],
            };

            // if let MicroMirStatement::BorrowMut(p_from, p_to) = statement {
            //     // println!("{:?}\t{:?}", location, pcs);
            //     // println!("{:?}\t{:?}", location, statement);
            //     // op_mir.statements.push(statement.clone());
            //     // op_mir.pcs_before.push(pcs.clone());

            //     if p_from.ty(&self.mir.local_decls, self.env.tcx()).ty.is_ref() {
            //         // p_from is a borrow (so it's in the reborrow DAG)
            //         todo!();
            //         pcs.dag
            //             .mutable_borrow(*p_from, parent_loan, *p_to, self.mir, self.env.tcx());
            //         // EXPECT there are no annotations returned?
            //     } else {
            //         // p_from is not a borrow, so a new borrow needs to be created.
            //         // Both permissions now leave.
            //         let annotations = pcs.dag.mutable_borrow(
            //             *p_from,
            //             parent_loan,
            //             *p_to,
            //             self.mir,
            //             self.env.tcx(),
            //         );
            //         println!("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~");
            //         println!("The annotations are {:?}", annotations);
            //         println!("The PCS after is {:?}", pcs);
            //         println!("p_from is {:?}", p_from);
            //         println!("p_to is {:?}", p_to);

            //         // Apply some annotations?
            //     }

            //     assert!(pcs.free.remove(&PCSPermission {
            //         target: LinearResource::Mir((*p_from).clone()),
            //         kind: Exclusive,
            //     }));

            //     assert!(pcs.free.remove(&PCSPermission {
            //         target: LinearResource::Mir((*p_to).clone()),
            //         kind: Uninit,
            //     }));

            //     assert!(pcs.free.insert(PCSPermission {
            //         target: LinearResource::Mir((*p_to).clone()),
            //         kind: Exclusive,
            //     }));

            //     println!("The PCS after doing transformations is {:?}", pcs);
            // }

            // if let MicroMirStatement::BorrowMove(p_from, p_to) = statement {
            //     // println!("{:?}\t{:?}", location, pcs);
            //     // println!("{:?}\t{:?}", location, statement);
            //     // op_mir.statements.push(statement.clone());
            //     // op_mir.pcs_before.push(pcs.clone());

            //     pcs.dag.r#move(*p_to, *p_from, location);
            // }

            // 0. Apply loans expiring at a place

            // 1. Elaborate the state-dependent conditions
            let statement_precondition = self.elaborate_precondition(&statement, location)?;

            let statement_postcondition = self.elaborate_postcondition(&statement)?;

            // 2. Repack to precondition
            pcs = self.repack(pcs, &statement_precondition, op_mir)?;

            // 3. Statement is coherent: push
            println!("{:?}\t{:?}", location, pcs);
            println!("{:?}\t{:?}", location, statement);
            op_mir.statements.push(statement.clone());
            op_mir.pcs_before.push(pcs.clone());

            // 4. Apply statement's semantics to state.
            pcs = transform_pcs(pcs, &statement_precondition, &statement_postcondition)?;
            if let MicroMirStatement::BorrowMut(p_from, p_to) = statement {
                let parent_loan = self.polonius_info.get_loan_at_location(location);
                pcs.dag
                    .mutable_borrow(*p_from, parent_loan, *p_to, self.mir, self.env.tcx());
            } else if let MicroMirStatement::BorrowMove(p_from, p_to) = statement {
                pcs.dag.r#move(*p_to, *p_from, location);
            }
            println!("\tAfter all semantics: {:?}", pcs);

            // 5. Update loans
            if polonius_apply_places.contains(&statement_index) {
                println!("\tWORKING ON: apply loans");
                println!("\t{:?} {:?}", location, pcs);
                println!(
                    "\tlive loans {:?}",
                    self.polonius_info.get_all_active_loans(location)
                );

                let live_loans = self.polonius_info.get_all_active_loans(location);
                let active_loans = live_loans
                    .0
                    .into_iter()
                    .chain(live_loans.1.into_iter())
                    .collect::<FxHashSet<_>>();
                let graph_result = pcs.dag.unwind(&active_loans);

                println!("\tGRAPH RESULT. NEW PCS {:?}", pcs);

                // TODO: Print the annotations
                // TODO: What happens on a conditional?!?!
                let perms_into_graph = graph_result
                    .added
                    .iter()
                    .filter(|p| p.tag == None)
                    .map(|p| PCSPermission {
                        target: LinearResource::Mir(p.place),
                        kind: Exclusive,
                    })
                    .collect::<FxHashSet<_>>();

                // Repack so the required permissions are in the right state
                // pcs = self.repack(pcs, &perms_into_graph, op_mir)?;

                println!("\tinto of graph {:?}", perms_into_graph);

                let perms_out_of_graph = graph_result
                    .removed
                    .iter()
                    .filter(|p| p.tag == None)
                    .map(|p| PCSPermission {
                        target: LinearResource::Mir(p.place),
                        kind: Exclusive,
                    })
                    .collect::<FxHashSet<_>>();

                println!("\tout of graph {:?}", perms_out_of_graph);

                // println!("Attempting to insert {:?}", perms_out_of_graph);
                // for perm in perms_out_of_graph.into_iter() {
                //     assert!(pcs.free.insert(perm));
                // }

                println!("\tAnnotations: {:?}", graph_result.annotations);
                println!("\t\tDAG {:?}", pcs.dag);

                println!(
                    "\t\tUnconditionally Accessible {:?}",
                    pcs.dag.unconditionally_accessible()
                );
                // // Ensure any unconditioanlly accessible places are added back into the graph
                // for p in pcs.dag.unconditionally_accessible().iter() {
                //     // (Naive) just insert, don't check if it's already in there or conflicts?
                //     pcs.free.insert(PCSPermission {
                //         target: LinearResource::Mir((*p).clone()),
                //         kind: Exclusive,
                //     });
                // }
            }
        }

        Ok(pcs)
    }

    fn get_block_data(&self, bb: &BasicBlock) -> EncodingResult<&MicroMirData<'tcx>> {
        self.micro_mir.get(bb).ok_or(PrustiError::internal(
            "basic block out of bounds",
            MultiSpan::new(),
        ))
    }

    /// TODO
    ///   1. I do not know if bb0 is always the initial basic block
    ///   2. I certainly know that we do not always start with an empty PCS
    fn initial_state(&self) -> Vec<(BasicBlock, PCS<'tcx>)> {
        vec![((0 as u32).into(), PCS::empty())]
    }

    /// Modifies a PCS to be coherent with the initialization state
    fn trim_pcs(
        &self,
        next_bb: BasicBlock,
        pcs: &mut PCS<'tcx>,
        op_mir: &mut StraightOperationalMir<'tcx>,
    ) -> EncodingResult<PCS<'tcx>> {
        let mut ret_pcs = PCS {
            free: FxHashSet::default(),
            dag: Single(Graph::default()),
        };

        let init_set = self.init_analysis.get_before_block(next_bb);
        let alloc_set = self.alloc_analysis.get_before_block(next_bb);

        // 1. Iterate over all the permissions, weakening the exclusive permissions
        let work_set = pcs.free.clone();

        for perm in work_set.iter() {
            match perm.target {
                LinearResource::Tmp(_) => {
                    // 1.1. Temporaries cannot be joined, ever.
                    return Err(PrustiError::internal(
                        "temporaries cannot be joined",
                        MultiSpan::new(),
                    ));
                }

                LinearResource::Mir(p) => {
                    let to_add = if perm.kind == Exclusive {
                        self.weaken_exclusive(p, init_set, alloc_set, op_mir, pcs)?
                    } else {
                        self.singleton_permission_set(perm.kind, p)
                    };

                    for t in to_add {
                        if !ret_pcs.free.insert(t) {
                            return Err(PrustiError::internal(
                                "unexpected incoherence in trimming",
                                MultiSpan::new(),
                            ));
                        }
                    }
                }
            }
        }

        // Check that the uninit permissions in ret_pcs are OK

        for ret_perm in ret_pcs.free.iter() {
            match ret_perm.target {
                LinearResource::Tmp(_) => {
                    // Impossible.
                    panic!()
                }
                LinearResource::Mir(p) => {
                    if (ret_perm.kind == Uninit) && !alloc_set.contains_prefix_of(p) {
                        return Err(PrustiError::internal(
                            "cannot weaken uninit permission to no permission",
                            MultiSpan::new(),
                        ));
                    }

                    if (ret_perm.kind == Uninit)
                        && (init_set.contains(p) || init_set.contains_subplace_of(p))
                    {
                        return Err(PrustiError::internal(
                            "uninit permission's footprint supposed to contain an init permission",
                            MultiSpan::new(),
                        ));
                    }
                }
            }
        }

        return Ok(ret_pcs);
    }

    // TODO: Either refactor somewhere else
    fn singleton_permission_set(
        &self,
        kind: PCSPermissionKind,
        p: Place<'tcx>,
    ) -> FxHashSet<PCSPermission<'tcx>> {
        [PCSPermission {
            kind,
            target: p.into(),
        }]
        .iter()
        .cloned()
        .collect()
    }

    // TODO: Refactor all weakenings into src/joins
    fn weaken_exclusive(
        &self,
        p: Place<'tcx>,
        init_set: &PlaceSet<'tcx>,
        alloc_set: &LocalSet,
        op_mir: &mut StraightOperationalMir<'tcx>,
        pcs: &mut PCS<'tcx>,
    ) -> EncodingResult<FxHashSet<PCSPermission<'tcx>>> {
        if init_set.contains(p) {
            // p is immediately in the init set... done
            Ok(self.singleton_permission_set(Exclusive, p))
        } else if init_set.contains_prefix_of(p) {
            // This is tentatively OK.
            // If all other (transitve) subplaces are init, the PCS can be repacked to match.
            // If even one other subplace is uninit, it will be detected by an uninit->exclusive weakening
            Ok(self.singleton_permission_set(Exclusive, p))
        } else if init_set.contains_subplace_of(p) {
            // Either all subplaces of the init_set are contained in the init_set
            //  and it is OK that p is init, or it only contains some init subplaces which is not OK
            let to_gain = expand_struct_place(p, self.mir, self.env.tcx(), None);
            op_mir.pcs_before.push(pcs.clone());
            op_mir
                .statements
                .push(MicroMirStatement::Unpack(p.clone(), to_gain.clone()));

            if !pcs
                .free
                .remove(&PCSPermission::new_initialized(Mut, p.into()))
            {
                return Err(PrustiError::internal(
                    "incoherent unpack preconidtion in trimming",
                    MultiSpan::new(),
                ));
            }

            for p1 in to_gain.iter() {
                if !pcs
                    .free
                    .insert(PCSPermission::new_initialized(Mut, (*p1).into()))
                {
                    return Err(PrustiError::internal(
                        "incoherent unpack postcondition in trimming",
                        MultiSpan::new(),
                    ));
                }
            }

            // Recursively check the initialilization of the new subplaces and collect the result
            // Must not just return to_gain, since there may be transitive unpacks
            // It is OK to do these one at a time, since their footprints are disjoint.
            let mut return_perms: FxHashSet<PCSPermission<'tcx>> = FxHashSet::default();
            for p1 in to_gain.iter() {
                let rec_ret = self.weaken_exclusive(*p1, init_set, alloc_set, op_mir, pcs)?;
                for rp in rec_ret {
                    return_perms.insert(rp);
                }
            }

            Ok(return_perms)
        }
        // Our place is initialized, but it's footprint overlaps nothing in the init set.
        // This means we genuinely have to weaken it to uninit if we are allowed to.
        else if alloc_set.contains_prefix_of(p) {
            // TODO: Log this eager drop somewhere
            Ok(self.singleton_permission_set(Uninit, p))
        } else {
            // We are not allowed to weaken the permission at all.
            Err(PrustiError::internal(
                "exclusive permission weakening failed",
                MultiSpan::new(),
            ))
        }
    }

    /// Elaborate the precondition of a statement
    fn elaborate_precondition(
        &self,
        stmt: &'mir MicroMirStatement<'tcx>,
        location: Location,
    ) -> EncodingResult<PCS<'tcx>> {
        if let Some(r) = stmt.precondition() {
            return Ok(r);
        }

        // State-dependent preconditions we can elaborate:
        //   - Kill of a MIR place
        //          INIT p => { e p }
        //          ALLOC p & !INIT p => { u p }
        match stmt {
            MicroMirStatement::Kill(None, LinearResource::Mir(p)) => {
                self.analysis_as_permission(p, location).ok_or_else(|| {
                    PrustiError::internal(
                        format!("could not find permission {:?} in analyses", p),
                        MultiSpan::new(),
                    )
                })
            }

            _ => Err(PrustiError::unsupported(
                "unsupported kill elaboration",
                MultiSpan::new(),
            )),
        }
    }

    // TODO: contains prefix of??
    // What about partial drops?
    fn analysis_as_permission(&self, p: &Place<'tcx>, location: Location) -> Option<PCS<'tcx>> {
        if self
            .init_analysis
            .get_before_statement(location)
            .contains_prefix_of(*p)
        {
            Some(PCS::from_vec(vec![PCSPermission::new_initialized(
                Mutability::Mut,
                LinearResource::Mir(*p),
            )]))
        } else if self
            .alloc_analysis
            .get_before_statement(location)
            .contains_prefix_of(*p)
        {
            Some(PCS::from_vec(vec![PCSPermission::new_uninit(
                LinearResource::Mir(*p),
            )]))
        } else if LinearResource::new_from_local_id(0) == LinearResource::Mir(*p) {
            // if _0 is not mentioned, assume uninit _0
            // probably *fine* because _0 is SSA but this is a hack
            Some(PCS::from_vec(vec![]))
            // Some(PCSPermission::new_uninit(
            //     LinearResource::new_from_local_id(0),
            // ))
        } else {
            None
        }
    }

    fn elaborate_postcondition(
        &self,
        stmt: &'mir MicroMirStatement<'tcx>,
    ) -> EncodingResult<PCS<'tcx>> {
        stmt.postcondition().ok_or(PrustiError::unsupported(
            "postconditions can not be elaborated",
            MultiSpan::new(),
        ))
    }

    /// Computes the unification between two PCS's, inserts packs and repacks as necessary
    fn repack(
        &self,
        pcs: PCS<'tcx>,
        next_pre: &PCS<'tcx>,
        op_mir: &mut StraightOperationalMir<'tcx>,
    ) -> EncodingResult<PCS<'tcx>> {
        RepackUnify::unify_moves(&pcs, next_pre, self.mir, self.env)?.apply_packings(
            pcs,
            &mut op_mir.statements,
            &mut op_mir.pcs_before,
        )
    }

    fn packup(
        &self,
        pcs: PCS<'tcx>,
        op_mir: &mut StraightOperationalMir<'tcx>,
    ) -> EncodingResult<PCS<'tcx>> {
        RepackPackup::new(self.env.tcx(), self.mir, pcs.clone())?.apply_packings(
            pcs,
            &mut op_mir.statements,
            &mut op_mir.pcs_before,
        )
    }

    // Note:
    //
    // PCS A -- repacks --.
    //                   join = PCS C
    // PCS B -- repacks --'
    //
    // as opposed to
    //
    // PCS A ----.
    //          join -- repacks --> PCS C
    // PCS B ----'
    //
    // as every unification done by the latter can be done by the former,
    //  but not vice-versa.

    // Actually! We're doing a different strategy.
    //
    // PCS A -- unpacks -- trim --.
    //                           join -- packs --> PCS C
    // PCS B -- unpacks -- trim --'
    //
    // - Theorem: All unifiable PCS's can be unified by doing packs, then unpacks
    //  (no interleaving necessary). That is, there is a meet-semilattice of permissions
    //
    // The trimming join enforces the following:
    //      - All exclusive permissions are exactly = init (alloc is a subset of init)
    //      - All uninit permissions are exactly = (init - alloc)
    //
}

/// TODO: Refactor this out from this file.
fn transform_pcs<'tcx>(
    mut pcs: PCS<'tcx>,
    pre: &PCS<'tcx>,
    post: &PCS<'tcx>,
) -> EncodingResult<PCS<'tcx>> {
    for p in pre.free.iter() {
        if !pcs.free.remove(p) {
            return Err(PrustiError::internal(
                format!("incoherent precondition: {:#?} in {:#?}", p, pcs.free),
                MultiSpan::new(),
            ));
        }
    }

    for p in post.free.iter() {
        if !pcs.free.insert((*p).clone()) {
            return Err(PrustiError::internal(
                format!("incoherent postcondition: {:#?} in {:#?}", p, pcs.free),
                MultiSpan::new(),
            ));
        }
    }

    return Ok(pcs);
}
