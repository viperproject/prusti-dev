use crate::modify_mir::mir_helper::{
    dummy_source_info, get_block_target, get_successors, replace_target,
};

use super::super::{mir_info_collector::MirInfo, mir_modifications::MirModifier};
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
    body_copy: Option<mir::Body<'tcx>>,
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
// we need to order them such that inserting checks will not offset other
// modifications
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
    pub fn new(
        tcx: TyCtxt<'tcx>,
        body_info: &'a MirInfo<'tcx>,
        def_id: DefId,
        local_decls: &'a IndexVec<mir::Local, mir::LocalDecl<'tcx>>,
    ) -> Self {
        Self {
            tcx,
            body_info,
            patch_opt: None,
            pledges_to_process: Default::default(),
            body_copy: None,
            def_id,
            local_decls,
            first_pass: true,
        }
    }

    pub fn run(&mut self, body: &mut mir::Body<'tcx>) {
        self.body_copy = Some(body.clone());
        self.patch_opt = Some(MirPatch::new(body).into());
        // find all calls to functions with pledges, and create local variables
        // to store: old_values, before_expiry_place,
        self.visit_body(body);
        // If there are no pledges, we can stop here.
        if self.pledges_to_process.is_empty() {
            return;
        }
        // only try to get polonius info after we know that there are indeed
        // pledges
        let procedure = Procedure::new(&self.body_info.env, self.def_id);
        let polonius_info = if let Some(info) = globals::get_polonius_info(self.def_id) {
            info
        } else {
            // for trusted methods this might not have been constructed before
            if let Ok(info) =
                PoloniusInfo::new(&self.body_info.env, &procedure, &FxHashMap::default())
            {
                info
            } else {
                // sometimes it seems to not be available for trusted methods.
                // Example: runtime_checks tests, shape.rs
                // I guess we don't just want to fail there, instead just don't
                // insert pledges.
                return;
            }
        };
        // apply the patch generated during visitation
        // this should only create new locals!
        let patcher_ref = self.patch_opt.take().unwrap();
        patcher_ref.into_inner().apply(body);

        // assumption: only one pledge associated with a loan.
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
                        let pledge = self.pledges_to_process.get(place).unwrap();
                        println!(
                            "Pledge for function {} is associated with loan {:?} and dies at {:?}",
                            pledge.name, loan, location
                        );
                    }
                }
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
                    // in this case we need to insert before the location
                    (
                        mir::Location {
                            block: *bb2,
                            statement_index: 0,
                        },
                        true,
                    )
                }
            };
            let either = body.stmt_at(location);
            if either.is_left() || is_edge {
                println!(
                    "Inserting a pledge check at arbitrary position. Pledge: {:?}, location: {:?}",
                    pledge, location
                );
                // it's just a statement: split the block
                // these modifications are not possible with MirPatch!
                let bb_data = &mut body.basic_blocks_mut()[location.block];
                let nr_stmts = bb_data.statements.len();
                let start_index = if !is_edge {
                    location.statement_index + 1
                } else {
                    0
                };
                // in the case of edges this will drain all statements
                let after = bb_data.statements.drain(start_index..nr_stmts);
                // create a new block:
                let term = bb_data.terminator.clone();
                let mut new_bb_data = mir::BasicBlockData::new(term);
                new_bb_data.statements = after.collect();
                self.patch_opt = Some(MirPatch::new(body).into());
                let new_block = self.patcher().new_block(new_bb_data);

                // create the checks:
                let (start_block, drop_insertion_block) =
                    self.create_pledge_call_chain(&pledge, new_block).unwrap();
                pledge.drop_blocks.push(drop_insertion_block);

                let new_terminator = mir::TerminatorKind::Goto {
                    target: start_block,
                };
                // skip this check block and instead call checks-chain
                self.patcher()
                    .patch_terminator(location.block, new_terminator);
                let patcher_ref = self.patch_opt.take().unwrap();
                patcher_ref.into_inner().apply(body);
            } else {
                let term = either.right().unwrap();
                self.patch_opt = Some(MirPatch::new(body).into());
                println!("inserting pledge expiration for terminator: {:?}", term);
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
                        replace_target(&mut new_call_term, start_block);
                        self.patcher()
                            .patch_terminator(location.block, new_call_term.kind);
                    }
                    _ => {
                        println!("Encountered a pledge expiring at terminator: {:#?}, expiring at location: {:?}", term, location);
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
        self.patch_opt = Some(MirPatch::new(body).into());
        for pledge in self.pledges_to_process.values() {
            for drop_block in pledge.drop_blocks.iter() {
                // get the target of the current drop block (always a goto,
                // exactly because we need to be able to append to it)
                if let Some(target) = get_block_target(body, *drop_block) {
                    let (chain_start, _) = self.create_drop_chain(
                        pledge.locals_to_drop.as_ref().unwrap().clone(),
                        Some(target),
                    );
                    let new_terminator = mir::TerminatorKind::Goto {
                        target: chain_start,
                    };
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
            // is a visit of the underlying things even necesary?
            if let Some((call_id, generics)) = func.const_fn_def() {
                for check_kind in self.body_info.specs.get_runtime_checks(&call_id) {
                    if let CheckKind::Pledge {
                        check,
                        check_before_expiry,
                    } = check_kind
                    {
                        if self.first_pass {
                            // TODO: pack that into a function, use correct param_env
                            let name = self.tcx.def_path_debug_str(call_id);
                            let check_sig = self.tcx.fn_sig(check).instantiate(self.tcx, generics);
                            let check_sig = self.tcx.normalize_erasing_late_bound_regions(
                                ty::ParamEnv::reveal_all(),
                                check_sig,
                            );
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
                            println!("Pledge result type: {:?}", result_ty);

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
                            println!("found pledge call, now prepending cloning");
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
        // mir::TerminatorKind::SwitchInt { targets, .. } => {
        //     // find switchInts with a check_only target.
        //     let switch_iter = targets.iter();
        //     if switch_iter.len() == 1 {
        //         // let (value, target) = switch_iter.next().unwrap();
        //         let otherwise = targets.otherwise();
        //         // check if target is a check_block:
        //         if let Some(kind) = self.body_info.check_blocks.get(&otherwise) {
        //             match kind {
        //                 CheckBlockKind::PledgeExpires(local) => {
        //                     // this check_block should terminate with a goto always!
        //                     if let mir::TerminatorKind::Goto { ref target } =
        //                         self.body_copy.as_ref().unwrap()[otherwise]
        //                             .terminator
        //                             .clone()
        //                             .unwrap()
        //                             .kind
        //                     {
        //                         let pledge = self.pledges_to_process.get(local).expect(
        //                             "pledge expiration without an actual pledge,\
        //                                     seems like our assumption that calls of pledges are\
        //                                     always encountered before the expiration is wrong",
        //                         );
        //                         let start_block =
        //                             self.create_pledge_call_chain(pledge, *target).unwrap();
        //
        //                         let new_terminator = mir::TerminatorKind::Goto {
        //                             target: start_block,
        //                         };
        //                         // skip this check block and instead call checks-chain
        //                         self.patcher().patch_terminator(otherwise, new_terminator);
        //                     }
        //                 }
        //                 // nothing to do..
        //                 CheckBlockKind::RuntimeAssertion => (),
        //             }
        //         }
        //     }
        // }
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
