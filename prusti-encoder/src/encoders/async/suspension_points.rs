use std::collections::{HashMap, HashSet};

use prusti_interface::{environment::body::MirBody, specs::typed::ProcedureKind};
use prusti_rustc_interface::{
    middle::{
        mir::{self, visit::Visitor},
        ty,
    },
    span::def_id::DefId,
};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::VirCtxt;

/// Analyzes a method's CFG to determine its suspension point
pub struct SuspensionPointAnalysis;

#[derive(Clone, Debug)]
pub struct SuspensionPoint {
    pub label: u32,
    // the first BB of the busy loop, which is where invariants should be put
    pub loop_head: mir::BasicBlock,
    // DefId's of the closures containing the on_exit/on_entry conditions (if any)
    pub on_exit_closures: Vec<DefId>,
    pub on_entry_closures: Vec<DefId>,
    // the local containing the future as well as its pinned reference inside the busy loop
    pub future_local: mir::Local,
    pub pin_local: mir::Local,
    // the original local containing the future at the time of its construction
    // Note that this may not be set, e.g. because the future is lacking a specification (in which
    // case the constructor call is not being detected as such) or because this analysis was unable
    // to track the future to the suspension-point.
    pub original_future_local: Option<mir::Local>,
}

#[derive(Clone, Debug)]
pub struct SuspensionPointAnalysisOutput(pub Vec<SuspensionPoint>);

impl task_encoder::OutputRefAny for SuspensionPointAnalysisOutput {}

#[derive(Debug, Clone)]
pub struct SuspensionPointAnalysisError;

impl TaskEncoder for SuspensionPointAnalysis {
    task_encoder::encoder_cache!(SuspensionPointAnalysis);

    type TaskDescription<'vir> = DefId;

    type OutputFullLocal<'vir> = SuspensionPointAnalysisOutput;

    type EncodingError = SuspensionPointAnalysisError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let def_id = *task_key;
        deps.emit_output_ref(def_id, ())?;
        vir::with_vcx(|vcx| {
            let local_def_id = def_id
                .as_local()
                .expect("SuspensionPointAnalysis requires local item");
            let substs = ty::GenericArgs::identity_for_item(vcx.tcx(), def_id);
            let body = vcx
                .body_mut()
                .get_impure_fn_body(local_def_id, substs, None);

            let mut visitor = SuspensionPointVisitor::new(vcx, body.clone());
            visitor.visit_body(&body);

            // create the list of suspension-points by labeling all unannotated ones
            let labels: HashSet<u32> = visitor.candidates.iter().flat_map(|c| c.label).collect();
            let mut next_label = 1;
            let mut get_next_label = || -> u32 {
                while labels.contains(&next_label) {
                    next_label += 1;
                }
                next_label
            };

            // extract the DefId's of the closures containing on_exit/on_entry conditions
            let marker_closure_def_ids = |marker_call_bb: Option<mir::BasicBlock>| -> Vec<DefId> {
                let Some(marker_call_bb) = marker_call_bb else {
                    return Vec::new();
                };
                let terminator = body.basic_blocks[marker_call_bb].terminator();
                let mir::TerminatorKind::Call { ref args, .. } = terminator.kind else {
                    panic!("marker function BB should have call terminator")
                };
                assert_eq!(args.len(), 2, "on_exit_marker call should have 2 arguments");
                let arg_ty = args[1].ty(&body.local_decls, vcx.tcx());
                let ty::TyKind::Tuple(closure_tys) = arg_ty.kind() else {
                    panic!("second argument to marker function should be tuple")
                };
                closure_tys
                    .iter()
                    .map(|ty| {
                        let ty::TyKind::Closure(def_id, _) = ty.kind() else {
                            panic!("tuple element of argument to marker function should be closure")
                        };
                        *def_id
                    })
                    .collect()
            };

            // attempt to track the places containing futures from their construction to their
            // suspension-points in order to map back from suspension-points to their future's
            // constructor calls
            let mut fut_place_tracker = FuturePlaceTracker::new(vcx);
            fut_place_tracker.visit_body(&body);

            let suspension_points: Vec<SuspensionPoint> = visitor
                .candidates
                .into_iter()
                .map(|candidate| SuspensionPoint {
                    label: candidate.label.unwrap_or_else(&mut get_next_label),
                    on_exit_closures: marker_closure_def_ids(candidate.on_exit_marker),
                    loop_head: candidate.loop_head.unwrap(),
                    on_entry_closures: marker_closure_def_ids(candidate.on_entry_marker),
                    future_local: candidate.future_place.unwrap(),
                    pin_local: candidate.pin_place.unwrap(),
                    original_future_local: fut_place_tracker
                        .original_fut_place
                        .get(&candidate.into_future_call.unwrap())
                        .copied(),
                })
                .collect();

            let res = SuspensionPointAnalysisOutput(suspension_points);
            Ok((res, ()))
        })
    }
}

#[derive(Default)]
struct SuspensionPointCandidate {
    label: Option<u32>,
    future_place: Option<mir::Local>,
    pin_place: Option<mir::Local>,
    on_exit_marker: Option<mir::BasicBlock>,
    into_future_call: Option<mir::BasicBlock>,
    loop_head: Option<mir::BasicBlock>,
    on_entry_marker: Option<mir::BasicBlock>,
}

struct SuspensionPointVisitor<'vir> {
    vcx: &'vir VirCtxt<'vir>,
    body: MirBody<'vir>,
    candidates: Vec<SuspensionPointCandidate>,
}

impl<'vir> SuspensionPointVisitor<'vir> {
    fn new(vcx: &'vir VirCtxt<'vir>, body: MirBody<'vir>) -> Self {
        Self {
            vcx,
            body,
            candidates: Vec::new(),
        }
    }

    fn check_suspension_point(
        &self,
        block: mir::BasicBlock,
        data: &mir::BasicBlockData<'vir>,
    ) -> Option<SuspensionPointCandidate> {
        const INVALID_MARKER_MSG: &str =
            "detected use of marker function outside of suspension-point";
        let mut candidate = SuspensionPointCandidate::default();

        // the first BB must be a call to the on_exit marker or into_future
        let (fn_def_id, ret_place, _, next_bb) = check_function_call(data.terminator())?;
        let def_path = self.vcx.tcx().def_path_str(fn_def_id);

        // if the call is to into_future, we can continue
        let (pre_loop_fut_place, next_bb) = if def_path == "std::future::IntoFuture::into_future" {
            candidate.into_future_call = Some(block);
            (ret_place, next_bb)
        // otherwise, we first check for the into_future call
        } else if def_path == "prusti_contracts::suspension_point_on_exit_marker" {
            candidate.on_exit_marker = Some(block);
            let next_bb_data = &self.body.basic_blocks[next_bb];
            let Some((fn_def_id, ret_place, _, next_next_bb)) =
                check_function_call(next_bb_data.terminator())
            else {
                panic!("{INVALID_MARKER_MSG}");
            };
            if self.vcx.tcx().def_path_str(fn_def_id) != "std::future::IntoFuture::into_future" {
                panic!("{INVALID_MARKER_MSG}");
            }
            candidate.into_future_call = Some(next_bb);
            (ret_place, next_next_bb)
        } else {
            return None;
        };
        if !pre_loop_fut_place.projection.is_empty() {
            return None;
        }

        // generally, the next BB just moves the future to a different place for the busy loop.
        // it may contain some statements for analysis purposes, but should otherwise
        // contain only a single assignment
        let next_bb = {
            let data = &self.body.basic_blocks[next_bb];
            let fut_place = {
                let stmts: Result<Vec<&mir::Statement>, _> = data
                    .statements
                    .iter()
                    .filter_map(|stmt| match stmt.kind {
                        mir::StatementKind::Assign(..) => Some(Ok(stmt)),
                        mir::StatementKind::StorageLive(..)
                        | mir::StatementKind::StorageDead(..)
                        | mir::StatementKind::FakeRead(..) => None,
                        _ => Some(Err(format!("{stmt:?}"))),
                    })
                    .collect();
                let stmt = match stmts.as_deref() {
                    Ok([stmt]) => stmt,
                    _ => return None,
                };
                match stmt.kind {
                    mir::StatementKind::Assign(box (
                        new_place,
                        mir::Rvalue::Use(mir::Operand::Move(old_place)),
                    )) if old_place == pre_loop_fut_place => new_place,
                    _ => return None,
                }
            };
            let next_bb = match data.terminator().kind {
                mir::TerminatorKind::Goto { target } => target,
                _ => return None,
            };
            assert!(
                fut_place.projection.is_empty(),
                "expected no projections on place containing future"
            );
            candidate.future_place = Some(fut_place.local);
            next_bb
        };

        // the following BB should be the busy loop's head,
        // which solely consists of a `FalseUnwind` terminator
        let next_bb = {
            let data = &self.body.basic_blocks[next_bb];
            if !data.statements.is_empty() {
                return None;
            }
            match data.terminator().kind {
                mir::TerminatorKind::FalseUnwind {
                    real_target,
                    unwind: _,
                } => {
                    candidate.loop_head = Some(next_bb);
                    real_target
                }
                _ => return None,
            }
        };

        // inside the busy loop, a reference to the future is taken and pinned
        // TODO: verify what types of other statements can appear here (e.g. StorageDead)
        let next_bb = {
            let data = &self.body.basic_blocks[next_bb];
            let stmts: Result<Vec<&mir::Statement>, _> = data
                .statements
                .iter()
                .filter_map(|stmt| match stmt.kind {
                    mir::StatementKind::Assign(..) => Some(Ok(stmt)),
                    mir::StatementKind::StorageLive(..) => None,
                    _ => Some(Err(format!("{:?}", stmt))),
                })
                .collect();
            let (ref_stmt, reborrow_stmt) = match stmts.as_deref() {
                Ok([s1, s2]) => (s1, s2),
                _ => return None,
            };
            // the first statement should just take a mutable reference to the future
            let ref_place = match ref_stmt.kind {
                mir::StatementKind::Assign(box (
                    ref_place,
                    mir::Rvalue::Ref(
                        _,
                        mir::BorrowKind::Mut {
                            kind: mir::MutBorrowKind::Default,
                        },
                        src_place,
                    ),
                )) if src_place.local == candidate.future_place.unwrap()
                    && ref_place.projection.is_empty() =>
                {
                    ref_place
                }
                _ => return None,
            };
            // and the second should reborrow that reference to another place
            let reborrow_place = match reborrow_stmt.kind {
                mir::StatementKind::Assign(box (
                    reborrow_place,
                    mir::Rvalue::Ref(
                        _,
                        mir::BorrowKind::Mut {
                            kind: mir::MutBorrowKind::TwoPhaseBorrow,
                        },
                        mir::Place {
                            local: src_local,
                            projection,
                        },
                    ),
                )) if src_local == ref_place.local
                    && projection.len() == 1
                    && projection[0] == mir::ProjectionElem::Deref
                    && reborrow_place.projection.is_empty() =>
                {
                    reborrow_place
                }
                _ => return None,
            };
            // finally, the reborrowd reference is pinned
            let (fn_def_id, ret_place, args, next_bb) = check_function_call(data.terminator())?;
            match args[..] {
                [mir::Operand::Move(arg_place)] if arg_place == reborrow_place => {}
                _ => return None,
            }
            if self.vcx.tcx().def_path_str(fn_def_id) != "std::pin::Pin::<P>::new_unchecked"
                || !ret_place.projection.is_empty()
            {
                return None;
            }
            candidate.pin_place = Some(ret_place.local);
            next_bb
        };

        // the following should reassign the `ResumeTy` arg and call `get_context` on it
        // NOTE: from here on, we don't check the statements inside the BBs, as we don't track the
        // places they use or assign to and rely on just checking terminators
        let next_bb = {
            let data = &self.body.basic_blocks[next_bb];
            let (fn_def_id, _, _, next_bb) = check_function_call(data.terminator())?;
            if self.vcx.tcx().def_path_str(fn_def_id) != "std::future::get_context" {
                return None;
            }
            next_bb
        };

        // then, the future is polled
        let next_bb = {
            let data = &self.body.basic_blocks[next_bb];
            let (_, _, args, next_bb) = check_function_call(data.terminator())?;
            match args[..] {
                [mir::Operand::Move(arg_place), _]
                    if arg_place.local == candidate.pin_place.unwrap()
                        && arg_place.projection.is_empty() => {}
                _ => return None,
            };
            next_bb
        };

        // and control flow switches on the result's discriminant
        let (ready_bb, pending_bb) = {
            let terminator = self.body.basic_blocks[next_bb].terminator();
            let mir::TerminatorKind::SwitchInt {
                discr: _,
                ref targets,
            } = terminator.kind
            else {
                return None;
            };
            let targets = targets.iter().collect::<Vec<_>>();
            match targets[..] {
                [(0, ready_bb), (1, pending_bb)] => (ready_bb, pending_bb),
                _ => return None,
            }
        };

        // the pending branch should first yield, and then goto back to the loop target
        let next_bb = {
            let terminator = self.body.basic_blocks[pending_bb].terminator();
            match terminator.kind {
                mir::TerminatorKind::Yield { resume, .. } => resume,
                _ => return None,
            }
        };
        match self.body.basic_blocks[next_bb].terminator().kind {
            mir::TerminatorKind::Goto { target } if target == candidate.loop_head.unwrap() => {}
            _ => return None,
        };

        // the ready branch should follow a false edge, drop the places containing the future before
        // and during the busy loop and then possibly call the on_entry marker
        let mir::TerminatorKind::FalseEdge {
            real_target: next_bb,
            ..
        } = self.body.basic_blocks[ready_bb].terminator().kind
        else {
            return None;
        };
        let next_bb = match self.body.basic_blocks[next_bb].terminator().kind {
            mir::TerminatorKind::Drop { place, target, .. }
                if place.local == candidate.future_place.unwrap()
                    && place.projection.is_empty() =>
            {
                target
            }
            _ => return None,
        };
        let next_bb = match self.body.basic_blocks[next_bb].terminator().kind {
            mir::TerminatorKind::Drop { place, target, .. } if place == pre_loop_fut_place => {
                target
            }
            _ => return None,
        };
        let terminator = self.body.basic_blocks[next_bb].terminator();
        if let Some((fn_def_id, _, args, _)) = check_function_call(terminator) {
            if self.vcx.tcx().def_path_str(fn_def_id)
                == "prusti_contracts::suspension_point_on_entry_marker"
            {
                let [mir::Operand::Constant(box lbl_const), _] = args[..] else {
                    panic!("invalid arguments to on_entry marker")
                };
                let mir::ConstantKind::Val(lbl_val, _) = lbl_const.literal else {
                    panic!("invalid arguments to on_entry marker")
                };
                let lbl = lbl_val
                    .try_to_scalar_int()
                    .expect("could not convert label value to u32")
                    .try_to_u32()
                    .expect("could not convert label scalar to u32");
                candidate.label = Some(lbl);
                candidate.on_entry_marker = Some(next_bb);
            }
        }

        // make sure markers can only appear as pairs
        assert_eq!(
            candidate.on_exit_marker.is_some(),
            candidate.on_entry_marker.is_some(),
            "found unpaired call to suspension-point marker function"
        );

        assert!(candidate.future_place.is_some());
        assert!(candidate.pin_place.is_some());
        assert!(candidate.into_future_call.is_some());
        assert!(candidate.loop_head.is_some());
        Some(candidate)
    }
}

/// Check if the terminator corresponds to a function call and if so, return that function's
/// DefId, the place for the return value, and the BB to continue with.
/// Function calls that necessarily diverge are *not* considered here.
fn check_function_call<'vir, 'a>(
    terminator: &'a mir::Terminator<'vir>,
) -> Option<(
    DefId,
    mir::Place<'vir>,
    &'a Vec<mir::Operand<'vir>>,
    mir::BasicBlock,
)> {
    let mir::TerminatorKind::Call {
        ref func,
        destination,
        ref target,
        ref args,
        ..
    } = terminator.kind
    else {
        return None;
    };
    let mir::Operand::Constant(box ref cnst) = func else {
        return None;
    };
    let mir::ConstantKind::Val(_, ty) = cnst.literal else {
        return None;
    };
    let ty::TyKind::FnDef(fn_def_id, _) = ty.kind() else {
        return None;
    };
    Some((*fn_def_id, destination, args, *target.as_ref()?))
}

impl<'vir> Visitor<'vir> for SuspensionPointVisitor<'vir> {
    fn visit_basic_block_data(&mut self, block: mir::BasicBlock, data: &mir::BasicBlockData<'vir>) {
        // if this BB is the into_future call of an already detected, annotated suspension-point,
        // we need to avoid detecting it as an unannotated one again
        if self
            .candidates
            .iter()
            .any(|candidate| candidate.into_future_call.unwrap() == block)
        {
            return;
        }

        // otherwise, just check if there is a suspension-point starting at this BB
        if let Some(candidate) = self.check_suspension_point(block, data) {
            self.candidates.push(candidate);
        }
    }
}

struct FuturePlaceTracker<'vir> {
    vcx: &'vir VirCtxt<'vir>,
    // tracking list mapping places to the original local their future was assigned to
    current_fut_place: HashMap<mir::Place<'vir>, mir::Local>,
    // finalized list mapping BBs of `into_future` calls to the original locals
    // containing their futures upon construction
    original_fut_place: HashMap<mir::BasicBlock, mir::Local>,
}

impl<'vir> FuturePlaceTracker<'vir> {
    fn new(vcx: &'vir VirCtxt<'vir>) -> Self {
        Self {
            vcx,
            current_fut_place: HashMap::new(),
            original_fut_place: HashMap::new(),
        }
    }
}

impl<'vir> Visitor<'vir> for FuturePlaceTracker<'vir> {
    fn visit_basic_block_data(&mut self, block: mir::BasicBlock, data: &mir::BasicBlockData<'vir>) {
        // visit all statements in the BB
        self.super_basic_block_data(block, data);

        // if this block calls a future constructor, add the local the future is being assigned to
        // to the tracking list
        let Some((fn_def_id, dest, args, _)) = check_function_call(data.terminator()) else {
            return;
        };
        let proc_kind = crate::encoders::with_proc_spec(fn_def_id, |proc_spec| proc_spec.proc_kind);
        if matches!(proc_kind, Some(ProcedureKind::AsyncConstructor)) {
            assert!(
                dest.projection.is_empty(),
                "expected future constructor to assign to local without projections"
            );
            self.current_fut_place.insert(dest, dest.local);
            return;
        }

        // if this block ends with an `IntoFuture::into_future` call, we can stop tracking that
        // future
        if self.vcx.tcx().def_path_str(fn_def_id) == "std::future::IntoFuture::into_future" {
            assert!(
                dest.projection.is_empty(),
                "expected `IntoFuture::into_future` to assign to unprojected local"
            );
            let [mir::Operand::Move(place)] = args[..] else {
                panic!("`IntoFuture::into_future` call should have exactly one moved argument");
            };
            if let Some(original_local) = self.current_fut_place.remove(&place) {
                self.original_fut_place.insert(block, original_local);
            };
        }
    }

    fn visit_statement(&mut self, statement: &mir::Statement<'vir>, _location: mir::Location) {
        // if this statement is an assignment, check if any of the tracked futures has moved
        // NOTE: we only track futures being moved to different places, and not e.g. being
        // referenced and then moved.
        let mir::StatementKind::Assign(box (
            new_place,
            mir::Rvalue::Use(mir::Operand::Move(old_place)),
        )) = statement.kind
        else {
            return;
        };

        // if the old place being moved out of was in the tracking list, change it so the new place
        // points to the original local
        if let Some(original_local) = self.current_fut_place.remove(&old_place) {
            self.current_fut_place.insert(new_place, original_local);
        }
    }
}
