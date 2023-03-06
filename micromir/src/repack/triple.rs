// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::middle::mir::RETURN_PLACE;

use crate::{
    FreeStateUpdate, MicroFullOperand, MicroStatement, MicroStatementKind, MicroTerminator,
    MicroTerminatorKind, Operands, PermissionKind,
};

pub(crate) trait ModifiesFreeState<'tcx> {
    fn get_update(&self, locals: usize) -> FreeStateUpdate<'tcx>;
}

impl<'tcx> ModifiesFreeState<'tcx> for Operands<'tcx> {
    #[tracing::instrument(level = "trace")]
    fn get_update(&self, locals: usize) -> FreeStateUpdate<'tcx> {
        let mut update = FreeStateUpdate::default(locals);
        for operand in &**self {
            match *operand {
                MicroFullOperand::Copy(place) => {
                    update[place.local].requires_alloc(
                        place,
                        &[PermissionKind::Exclusive, PermissionKind::Shared],
                    );
                }
                MicroFullOperand::Move(place) => {
                    update[place.local].requires_alloc_one(place, PermissionKind::Exclusive);
                    update[place.local].ensures_alloc(place, PermissionKind::Uninit);
                }
                MicroFullOperand::Constant(..) => (),
            }
        }
        update
    }
}

impl<'tcx> ModifiesFreeState<'tcx> for MicroStatement<'tcx> {
    #[tracing::instrument(level = "trace")]
    fn get_update(&self, locals: usize) -> FreeStateUpdate<'tcx> {
        let mut update = self.operands.get_update(locals);
        match &self.kind {
            &MicroStatementKind::Assign(box (place, _)) => {
                if let Some(pre) = update[place.local].get_pre_for(place) {
                    assert_eq!(pre.len(), 2);
                    assert!(pre.contains(&PermissionKind::Exclusive));
                    assert!(pre.contains(&PermissionKind::Shared));
                } else {
                    update[place.local].requires_alloc_one(place, PermissionKind::Uninit);
                }
                update[place.local].ensures_alloc(place, PermissionKind::Exclusive);
            }
            MicroStatementKind::FakeRead(box (_, place)) => update[place.local]
                .requires_alloc(*place, &[PermissionKind::Exclusive, PermissionKind::Shared]),
            MicroStatementKind::SetDiscriminant { box place, .. } => {
                update[place.local].requires_alloc_one(*place, PermissionKind::Exclusive)
            }
            MicroStatementKind::Deinit(box place) => {
                // TODO: Maybe OK to also allow `Uninit` here?
                update[place.local].requires_alloc_one(*place, PermissionKind::Exclusive);
                update[place.local].ensures_alloc(*place, PermissionKind::Uninit);
            }
            &MicroStatementKind::StorageLive(local) => {
                update[local].requires_unalloc();
                update[local].ensures_alloc(local.into(), PermissionKind::Uninit);
            }
            &MicroStatementKind::StorageDead(local) => {
                update[local].requires_unalloc_or_uninit(local);
                update[local].ensures_unalloc();
            }
            MicroStatementKind::Retag(_, box place) => {
                update[place.local].requires_alloc_one(*place, PermissionKind::Exclusive)
            }
            MicroStatementKind::AscribeUserType(..)
            | MicroStatementKind::Coverage(..)
            | MicroStatementKind::Intrinsic(..)
            | MicroStatementKind::ConstEvalCounter
            | MicroStatementKind::Nop => (),
        };
        update
    }
}

impl<'tcx> ModifiesFreeState<'tcx> for MicroTerminator<'tcx> {
    #[tracing::instrument(level = "trace")]
    fn get_update(&self, locals: usize) -> FreeStateUpdate<'tcx> {
        let mut update = self.operands.get_update(locals);
        match &self.kind {
            MicroTerminatorKind::Goto { .. }
            | MicroTerminatorKind::SwitchInt { .. }
            | MicroTerminatorKind::Resume
            | MicroTerminatorKind::Abort
            | MicroTerminatorKind::Unreachable
            | MicroTerminatorKind::Assert { .. }
            | MicroTerminatorKind::GeneratorDrop
            | MicroTerminatorKind::FalseEdge { .. }
            | MicroTerminatorKind::FalseUnwind { .. } => (),
            MicroTerminatorKind::Return => update[RETURN_PLACE]
                .requires_alloc_one(RETURN_PLACE.into(), PermissionKind::Exclusive),
            MicroTerminatorKind::Drop { place, .. } => {
                update[place.local]
                    .requires_alloc(*place, &[PermissionKind::Exclusive, PermissionKind::Uninit]);
                update[place.local].ensures_alloc(*place, PermissionKind::Uninit);
            }
            MicroTerminatorKind::DropAndReplace { place, .. } => {
                update[place.local]
                    .requires_alloc(*place, &[PermissionKind::Exclusive, PermissionKind::Uninit]);
                update[place.local].ensures_alloc(*place, PermissionKind::Exclusive);
            }
            MicroTerminatorKind::Call { destination, .. } => {
                update[destination.local].requires_alloc_one(*destination, PermissionKind::Uninit);
                update[destination.local].ensures_alloc(*destination, PermissionKind::Exclusive);
            }
            MicroTerminatorKind::Yield { resume_arg, .. } => {
                update[resume_arg.local].requires_alloc_one(*resume_arg, PermissionKind::Uninit);
                update[resume_arg.local].ensures_alloc(*resume_arg, PermissionKind::Exclusive);
            }
        };
        update
    }
}
