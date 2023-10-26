use super::super::{mir_info_collector::MirInfo, mir_modifications::MirModifier};
use crate::modify_mir::mir_helper::{
    dummy_source_info, fn_signature, get_goto_block_target, get_successors, replace_call_target,
};
use prusti_interface::{
    environment::{borrowck::facts::Loan, polonius_info::PoloniusInfo, Procedure},
    globals,
    specs::typed::CheckKind,
};
use prusti_rustc_interface::{
    index::IndexVec,
    middle::{
        mir::{self, patch::MirPatch, visit::MutVisitor},
        ty::{self, TyCtxt},
    },
    span::{def_id::DefId, DUMMY_SP},
};
use rustc_hash::FxHashMap;
use std::{
    cell::{RefCell, RefMut},
    cmp::Ordering,
};

pub struct PledgeInserter<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    body_info: &'a MirInfo<'tcx>,
    patch_opt: Option<RefCell<MirPatch<'tcx>>>,
    pledges_to_process: FxHashMap<mir::Place<'tcx>, PledgeToProcess<'tcx>>,
    def_id: DefId,
    local_decls: &'a IndexVec<mir::Local, mir::LocalDecl<'tcx>>,
    /// For simplicity we use the same visitor twice, once to find all the
    /// calls with pledges, create locals and extract information, but without
    /// shifting any locations in the MIR, on the second one we prepend the
    /// old and before_expiry storing, and setting the guard booleans
    /// before each call.
    first_pass: bool,
}

#[derive(PartialEq, Eq, Clone, Copy)]
enum ExpirationLocation {
    Location(mir::Location),
    Edge(mir::BasicBlock, mir::BasicBlock),
}

impl ExpirationLocation {
    fn block(&self) -> mir::BasicBlock {
        match self {
            ExpirationLocation::Location(loc) => loc.block,
            // for edges we only modify the second block
            ExpirationLocation::Edge(_, bb) => *bb,
        }
    }
    fn statement_index(&self) -> usize {
        match self {
            Self::Location(loc) => loc.statement_index + 1,
            Self::Edge(_, _) => 0,
        }
    }
}
// we need to order them by descending block and statement index such that inserting
// checks will not offset the modifications that will be inserted later
impl PartialOrd for ExpirationLocation {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for ExpirationLocation {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.block().cmp(&other.block()) {
            Ordering::Equal => self.statement_index().cmp(&other.statement_index()),
            other => other,
        }
    }
}

#[derive(Debug, Clone)]
pub struct PledgeToProcess<'tcx> {
    pub name: String,
    pub check: DefId,
    pub check_before_expiry: Option<DefId>,
    pub result_copy_place: mir::Place<'tcx>,
    pub old_values_place: mir::Place<'tcx>,
    pub old_values_ty: ty::Ty<'tcx>,
    pub before_expiry_place: mir::Place<'tcx>,
    pub before_expiry_ty: ty::Ty<'tcx>,
    pub destination: mir::Place<'tcx>,
    // the args the function was called with
    pub args: Vec<mir::Operand<'tcx>>,
    pub generics: ty::GenericArgsRef<'tcx>,
    // a local that is set when a function with a pledge is called
    // and then checked before a runtime check at an expiration location
    // is performed.
    pub guard_place: mir::Place<'tcx>,
    pub location: mir::Location,
    pub drop_blocks: Vec<mir::BasicBlock>,
    pub locals_to_drop: Option<Vec<mir::Local>>,
}

impl<'tcx, 'a> PledgeInserter<'tcx, 'a> {
    pub fn run(
        tcx: TyCtxt<'tcx>,
        body_info: &'a MirInfo<'tcx>,
        def_id: DefId,
        local_decls: &'a IndexVec<mir::Local, mir::LocalDecl<'tcx>>,
        body: &mut mir::Body<'tcx>,
    ) {
        let mut inserter = Self {
            tcx,
            body_info,
            patch_opt: Some(MirPatch::new(body).into()),
            pledges_to_process: Default::default(),
            def_id,
            local_decls,
            first_pass: true,
        };
        inserter.modify(body);
    }

    fn modify(&mut self, body: &mut mir::Body<'tcx>) {
        // find all calls to functions with pledges, and create local variables
        // to store: old_values, before_expiry_place,
        self.visit_body(body);
        // If there are no pledges, we can stop here.
        if self.pledges_to_process.is_empty() {
            return;
        }
        // apply the patch generated during visitation
        // this should only create new locals!
        let patcher_ref = self.patch_opt.take().unwrap();
        patcher_ref.into_inner().apply(body);

        let procedure = Procedure::new(&self.body_info.env, self.def_id);
        let polonius_info = if let Some(info) = globals::get_polonius_info(self.def_id) {
            info
        } else {
            // for trusted methods this might not have been constructed before
            PoloniusInfo::new(&self.body_info.env, &procedure, &FxHashMap::default()).unwrap()
        };

        // collect the loans that belong to some call with a pledge attached
        let pledge_loans: FxHashMap<Loan, mir::Place<'tcx>> = self
            .pledges_to_process
            .iter()
            .map(|(place, PledgeToProcess { location, .. })| {
                (
                    polonius_info.get_call_loan_at_location(*location).unwrap(),
                    *place,
                )
            })
            .collect();
        // Now, use polonius to find all expiration locations:
        // note: each pledge can potentially expire in multiple locations:
        let mut modification_list: Vec<(ExpirationLocation, mir::Place<'tcx>)> = Vec::new();
        for (bb, bb_data) in body.basic_blocks.iter_enumerated() {
            let nr_statements = bb_data.statements.len();
            for statement_index in 0..nr_statements + 1 {
                let location = mir::Location {
                    block: bb,
                    statement_index,
                };
                let loans_dying = polonius_info.get_loans_dying_at(location, false);
                for loan in loans_dying.iter() {
                    // check if any of the loans are associated with one of
                    // our pledges:
                    if let Some(place) = pledge_loans.get(loan) {
                        // a pledge is associated with this loan and dies here!!
                        modification_list.push((ExpirationLocation::Location(location), *place));
                    }
                }
                // For switchInts, also look at the expirations of loans on edges, since
                // in that case they can not be found when simply looking at the location
                if statement_index == nr_statements
                    && matches!(
                        body[bb].terminator.as_ref().unwrap().kind,
                        mir::TerminatorKind::SwitchInt { .. }
                    )
                {
                    let successors = get_successors(body, location);
                    for successor in successors.iter() {
                        let loans_dying =
                            polonius_info.get_loans_dying_between(location, *successor, false);
                        for loan in loans_dying {
                            if let Some(place) = pledge_loans.get(&loan) {
                                modification_list
                                    .push((ExpirationLocation::Edge(bb, successor.block), *place));
                            }
                        }
                    }
                }
            }
        }
        // sort the modification list according to location, so they
        // don't offset each other:
        modification_list.sort_by_key(|el| el.0);
        modification_list.reverse();
        // insert the checks:
        // store the places where we still need to insert drops
        // once we know which locals need to be dropped
        for (modification_location, place) in modification_list.iter() {
            // remove pledge temporarily so we can modify it
            let mut pledge = self.pledges_to_process.remove(place).unwrap();
            let (location, is_edge) = match modification_location {
                ExpirationLocation::Location(loc) => (*loc, false),
                ExpirationLocation::Edge(_, bb2) => {
                    // in case of an edge, we will insert the check at index 0
                    // of the block the edge points to
                    (
                        mir::Location {
                            block: *bb2,
                            statement_index: 0,
                        },
                        true,
                    )
                }
            };
            let either_stmt_or_terminator = body.stmt_at(location);
            if either_stmt_or_terminator.is_left() || is_edge {
                // it's just a statement: split the block.
                let bb_data = &mut body.basic_blocks_mut()[location.block];
                let nr_stmts = bb_data.statements.len();
                let start_index = if !is_edge {
                    location.statement_index + 1
                } else {
                    0
                };
                // in the case of edges this will drain all statements
                let after = bb_data.statements.drain(start_index..nr_stmts);
                // create a new block with the original block's terminator and all
                // the statements following our location:
                let term = bb_data.terminator.clone();
                let mut new_bb_data = mir::BasicBlockData::new(term);
                new_bb_data.statements = after.collect();
                self.patch_opt = Some(MirPatch::new(body).into());
                let new_block = self.patcher().new_block(new_bb_data);

                // create the check call chain that continues executing new_block once
                // the checks are done:
                let (start_block, drop_insertion_block) =
                    self.create_pledge_call_chain(&pledge, new_block).unwrap();
                // store the drop insertion block so we can later insert the required
                // drops
                pledge.drop_blocks.push(drop_insertion_block);

                let new_terminator = mir::TerminatorKind::Goto {
                    target: start_block,
                };
                // override the original terminator to point to our check-chain
                self.patcher()
                    .patch_terminator(location.block, new_terminator);
                let patcher_ref = self.patch_opt.take().unwrap();
                patcher_ref.into_inner().apply(body);
            } else {
                // In this case, we want to insert our check after a terminator
                let term = either_stmt_or_terminator.right().unwrap();
                self.patch_opt = Some(MirPatch::new(body).into());
                match term.kind {
                    mir::TerminatorKind::Call {
                        target: Some(target),
                        ..
                    } => {
                        // create the call chain with the calls target:
                        let (start_block, drop_insertion_block) =
                            self.create_pledge_call_chain(&pledge, target).unwrap();
                        // we need to store the block where we can later insert
                        // the drops for values we cloned for old
                        pledge.drop_blocks.push(drop_insertion_block);

                        let mut new_call_term = term.clone();
                        // After the call is finished, jump to our check-chain
                        replace_call_target(&mut new_call_term, start_block);
                        self.patcher()
                            .patch_terminator(location.block, new_call_term.kind);
                    }
                    _ => {
                        // Can pledges expire at other kinds of terminators?
                        todo!()
                    }
                }
                let patcher_ref = self.patch_opt.take().unwrap();
                patcher_ref.into_inner().apply(body);
            }
            // insert pledge again.
            self.pledges_to_process.insert(*place, pledge);
        }

        // run the visitor again, now for phase 2: inserting the cloning
        self.patch_opt = Some(MirPatch::new(body).into());
        self.first_pass = false;
        self.visit_body(body);
        let patcher_ref = self.patch_opt.take().unwrap();
        patcher_ref.into_inner().apply(body);

        // finally, drop the old values at each expiration check:
        // We do this here, because cloning all the values when we traverse the MIR
        // the first time, would offset locations. Only after cloning do we actually
        // know which values will need to be dropped.
        self.patch_opt = Some(MirPatch::new(body).into());
        for pledge in self.pledges_to_process.values() {
            for drop_block in pledge.drop_blocks.iter() {
                // get the target of the current drop block (always a goto,
                // exactly because we need to be able to append to it)
                if let Some(target) = get_goto_block_target(body, *drop_block) {
                    let (chain_start, _) = self.create_drop_chain(
                        pledge.locals_to_drop.as_ref().unwrap().clone(),
                        Some(target),
                    );
                    let new_terminator = mir::TerminatorKind::Goto {
                        target: chain_start,
                    };
                    // make the drop block, which we created earlier point the the drop chain
                    self.patcher().patch_terminator(*drop_block, new_terminator);
                } else {
                    unreachable!();
                }
            }
        }
        // apply patcher for a final time
        let patcher_ref = self.patch_opt.take().unwrap();
        patcher_ref.into_inner().apply(body);
    }

    /// This generates a BasicBlock that does the following:
    /// If a pledge has been created, set it's corresponding guard to true,
    /// such that subsequent checks at expiration locations will be performed
    pub fn set_guard_true_block(
        &self,
        destination: mir::Place<'tcx>,
        target: mir::BasicBlock,
    ) -> mir::BasicBlock {
        let stmt_kind = self.set_bool_stmt(destination, true);
        let stmt = mir::Statement {
            source_info: dummy_source_info(),
            kind: stmt_kind,
        };
        let terminator = mir::Terminator {
            source_info: dummy_source_info(),
            kind: mir::TerminatorKind::Goto { target },
        };
        let mut new_block = mir::BasicBlockData::new(Some(terminator));
        new_block.statements.push(stmt);
        self.patcher().new_block(new_block)
    }
}

impl<'tcx, 'a> MutVisitor<'tcx> for PledgeInserter<'tcx, 'a> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_terminator(
        &mut self,
        terminator: &mut mir::Terminator<'tcx>,
        location: mir::Location,
    ) {
        if let mir::TerminatorKind::Call {
            func,
            destination,
            args,
            target,
            ..
        } = &terminator.kind
        {
            if let Some((call_id, generics)) = func.const_fn_def() {
                for check_kind in self.body_info.specs.get_runtime_checks(&call_id) {
                    if let CheckKind::Pledge {
                        check,
                        check_before_expiry,
                    } = check_kind
                    {
                        if self.first_pass {
                            let name = self.tcx.def_path_debug_str(call_id);
                            let check_sig = fn_signature(self.tcx, check, Some(generics));
                            let inputs = check_sig.inputs();
                            // look at the check function signature to determine
                            // which values need cloning.
                            let old_values_ty = inputs[inputs.len() - 2];
                            let before_expiry_ty = inputs[inputs.len() - 1];
                            // create temporary locals for them
                            let old_values_place =
                                mir::Place::from(self.patcher().new_temp(old_values_ty, DUMMY_SP));
                            let before_expiry_place = mir::Place::from(
                                self.patcher().new_temp(before_expiry_ty, DUMMY_SP),
                            );

                            // create a copy of the result in case it becomes a zombie later
                            let result_ty = destination.ty(self.local_decls(), self.tcx).ty;
                            let result_copy_place =
                                mir::Place::from(self.patcher().new_temp(result_ty, DUMMY_SP));

                            // create a guard local
                            let bool_ty = self.tcx.mk_ty_from_kind(ty::TyKind::Bool);
                            let local_guard = self.patcher().new_temp(bool_ty, DUMMY_SP).into();
                            let pledge_to_process = PledgeToProcess {
                                name,
                                check,
                                check_before_expiry,
                                result_copy_place,
                                old_values_place,
                                old_values_ty,
                                before_expiry_place,
                                before_expiry_ty,
                                destination: *destination,
                                args: args.clone(),
                                generics,
                                guard_place: local_guard,
                                location,
                                drop_blocks: Vec::new(),
                                locals_to_drop: None,
                            };
                            // TODO: create a test where the result is assigned
                            // to the field of a tuple
                            // Make sure this location is actually unique:
                            assert!(self.pledges_to_process.get(destination).is_none());
                            self.pledges_to_process
                                .insert(*destination, pledge_to_process);
                        } else {
                            let mut pledge = self.pledges_to_process.remove(destination).unwrap();
                            // create the clones of old that will be passed to
                            // the check function. Make the chain end with the
                            // original function call
                            let (chain_start, _new_caller, locals_to_drop) = self
                                .prepend_old_cloning(
                                    terminator.clone(),
                                    pledge.old_values_place,
                                    pledge.old_values_ty,
                                    args.clone(),
                                    true,
                                );
                            // those have yet to be dropped
                            pledge.locals_to_drop = Some(locals_to_drop);
                            let set_guard_block =
                                self.set_guard_true_block(pledge.guard_place, chain_start);
                            // of our function
                            self.patcher().patch_terminator(
                                location.block,
                                mir::TerminatorKind::Goto {
                                    target: set_guard_block,
                                },
                            );
                            // Copy the result after the function has been called:
                            // If it has a target, otherwise it doesn't matter at all..
                            if let Some(target) = target {
                                let location = mir::Location {
                                    block: *target,
                                    statement_index: 0,
                                };
                                let result_operand = mir::Operand::Copy(pledge.destination);
                                let stmt = mir::StatementKind::Assign(Box::new((
                                    pledge.result_copy_place,
                                    mir::Rvalue::Use(result_operand),
                                )));
                                self.patcher().add_statement(location, stmt);
                            }
                            self.pledges_to_process.insert(*destination, pledge);
                        }
                    }
                }
            }
        }
    }
}

impl<'tcx, 'a> MirModifier<'tcx> for PledgeInserter<'tcx, 'a> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn patcher(&self) -> RefMut<MirPatch<'tcx>> {
        self.patch_opt
            .as_ref()
            .expect("Bug: MirPatch was not initialized for MirModifier")
            .borrow_mut()
    }

    fn def_id(&self) -> DefId {
        self.def_id
    }

    fn local_decls(&self) -> &'a IndexVec<mir::Local, mir::LocalDecl<'tcx>> {
        self.local_decls
    }
}
