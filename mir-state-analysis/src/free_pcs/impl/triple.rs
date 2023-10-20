// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::{
    hir::Mutability,
    middle::mir::{
        visit::Visitor, BorrowKind, Local, Location, Operand, Rvalue, Statement, StatementKind,
        Terminator, TerminatorKind, RETURN_PLACE,
    },
};

use crate::free_pcs::{CapabilityKind, Fpcs};

impl<'tcx> Visitor<'tcx> for Fpcs<'_, 'tcx> {
    fn visit_operand(&mut self, operand: &Operand<'tcx>, location: Location) {
        self.super_operand(operand, location);
        match *operand {
            Operand::Copy(place) => {
                self.requires_read(place);
            }
            Operand::Move(place) => {
                self.requires_exclusive(place);
                self.ensures_write(place);
            }
            Operand::Constant(..) => (),
        }
    }

    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        self.super_statement(statement, location);
        use StatementKind::*;
        match &statement.kind {
            Assign(box (place, rvalue)) => {
                self.requires_write(*place);
                let ensures = rvalue.capability();
                match ensures {
                    CapabilityKind::Exclusive => self.ensures_exclusive(*place),
                    CapabilityKind::ShallowExclusive => self.ensures_shallow_exclusive(*place),
                    _ => unreachable!(),
                }
            }
            &FakeRead(box (_, place)) => self.requires_read(place),
            &SetDiscriminant { box place, .. } => self.requires_exclusive(place),
            &Deinit(box place) => {
                // TODO: Maybe OK to also allow `Write` here?
                self.requires_exclusive(place);
                self.ensures_write(place);
            }
            &StorageLive(local) => {
                self.requires_unalloc(local);
                self.ensures_allocates(local);
            }
            &StorageDead(local) => {
                self.requires_unalloc_or_uninit(local);
                self.ensures_unalloc(local);
            }
            &Retag(_, box place) => self.requires_exclusive(place),
            AscribeUserType(..) | PlaceMention(..) | Coverage(..) | Intrinsic(..) | ConstEvalCounter | Nop => (),
        };
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        self.super_terminator(terminator, location);
        use TerminatorKind::*;
        match &terminator.kind {
            Goto { .. }
            | SwitchInt { .. }
            | Resume
            | Terminate
            | Unreachable
            | Assert { .. }
            | GeneratorDrop
            | FalseEdge { .. }
            | FalseUnwind { .. } => (),
            Return => {
                let always_live = self.repacker.always_live_locals();
                for local in 0..self.repacker.local_count() {
                    let local = Local::from_usize(local);
                    if local == RETURN_PLACE {
                        self.requires_exclusive(RETURN_PLACE);
                    } else if always_live.contains(local) {
                        self.requires_write(local);
                    } else {
                        self.requires_unalloc(local);
                    }
                }
            }
            &Drop { place, replace: false, .. } => {
                self.requires_write(place);
                self.ensures_write(place);
            }
            &Drop { place, replace: true, .. } => {
                self.requires_write(place);
                self.ensures_exclusive(place);
            }
            &Call { destination, .. } => {
                self.requires_write(destination);
                self.ensures_exclusive(destination);
            }
            &Yield { resume_arg, .. } => {
                self.requires_write(resume_arg);
                self.ensures_exclusive(resume_arg);
            }
            InlineAsm { .. } => todo!("{terminator:?}"),
        };
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        self.super_rvalue(rvalue, location);
        use Rvalue::*;
        match rvalue {
            Use(_)
            | Repeat(_, _)
            | ThreadLocalRef(_)
            | Cast(_, _, _)
            | BinaryOp(_, _)
            | CheckedBinaryOp(_, _)
            | NullaryOp(_, _)
            | UnaryOp(_, _)
            | Aggregate(_, _)
            | ShallowInitBox(_, _) => {}

            &Ref(_, bk, place) => match bk {
                BorrowKind::Shared => {
                    self.requires_read(place);
                    // self.ensures_blocked_read(place);
                }
                // TODO: this should allow `Shallow Shared` as well
                BorrowKind::Shallow => {
                    self.requires_read(place);
                    // self.ensures_blocked_read(place);
                }
                BorrowKind::Mut { .. } => {
                    self.requires_exclusive(place);
                    // self.ensures_blocked_exclusive(place);
                }
            },
            &AddressOf(m, place) => match m {
                Mutability::Not => self.requires_read(place),
                Mutability::Mut => self.requires_exclusive(place),
            },
            &Len(place) => self.requires_read(place),
            &Discriminant(place) => self.requires_read(place),
            &CopyForDeref(place) => self.requires_read(place),
        }
    }
}

trait ProducesCapability {
    fn capability(&self) -> CapabilityKind;
}

impl ProducesCapability for Rvalue<'_> {
    fn capability(&self) -> CapabilityKind {
        use Rvalue::*;
        match self {
            Use(_)
            | Repeat(_, _)
            | Ref(_, _, _)
            | ThreadLocalRef(_)
            | AddressOf(_, _)
            | Len(_)
            | Cast(_, _, _)
            | BinaryOp(_, _)
            | CheckedBinaryOp(_, _)
            | NullaryOp(_, _)
            | UnaryOp(_, _)
            | Discriminant(_)
            | Aggregate(_, _)
            | CopyForDeref(_) => CapabilityKind::Exclusive,
            ShallowInitBox(_, _) => CapabilityKind::ShallowExclusive,
        }
    }
}
