// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![allow(dead_code)]

use crate::pcs::{MicroMirStatement, MicroMirTerminator, TemporaryPlace};
use rustc_middle::mir::{
    terminator::{Terminator, TerminatorKind::*},
    BasicBlock, BinOp, Body, Local, Mutability,
    Mutability::*,
    NullOp, Operand,
    Operand::*,
    Place,
    Rvalue::*,
    Statement,
    StatementKind::*,
    UnOp,
};

use rustc_middle::ty;

pub enum MicroMirEncodingError {
    UnsupportedStatementError(String),
    ExpectedMutableError(String),
    LocalError(String),
}

pub struct MicroMirEncoder<'mir, 'tcx: 'mir> {
    pub body: &'mir Body<'mir>,
    pub encoding: &'tcx Vec<Vec<MicroMirStatement<'tcx>>>,
}

/// TODO: For now I only have temporaries with exclusive permissions. Is this always the case?

impl<'mir, 'tcx: 'mir> MicroMirEncoder<'mir, 'tcx> {
    fn encode_individual_statement(
        &self,
        current: &mut Vec<MicroMirStatement<'tcx>>,
        s: &Statement<'tcx>,
    ) -> Result<(), MicroMirEncodingError> {
        match &s.kind {
            Assign(box (p_dest, Use(op))) => {
                return self.encode_assign_use(current, p_dest, op);
            }

            Assign(box (p_dest, Len(p0))) => {
                return self.encode_assign_len(current, p_dest, p0);
            }

            Assign(box (p_dest, BinaryOp(binop, box (op1, op2)))) => {
                return self.encode_binop(current, *binop, op1, op2, p_dest, false);
            }

            Assign(box (p_dest, CheckedBinaryOp(binop, box (op1, op2)))) => {
                return self.encode_binop(current, *binop, op1, op2, p_dest, true);
            }

            Assign(box (p_dest, UnaryOp(unop, op))) => {
                return self.encode_unop(current, *unop, op, p_dest);
            }

            Assign(box (p_dest, NullaryOp(nullop, _))) => {
                // TODO: The TY field here isn't used... but I think we'll need it when we lower to Viper.
                return self.encode_nullop(current, *nullop, p_dest);
            }

            us => {
                return Err(MicroMirEncodingError::UnsupportedStatementError(format!(
                    "Unsupported Statement: {:#?}",
                    us
                )))
            }
        }
    }

    /// Returns the terminator for a basic block, potentially appending micro-steps to current
    pub fn encode_terminator(
        &self,
        current: &mut Vec<MicroMirStatement<'tcx>>,
        t: &'tcx Terminator,
    ) -> Result<MicroMirTerminator<'tcx>, MicroMirEncodingError> {
        match &t.kind {
            Goto { target } => Ok(MicroMirTerminator::Jump(*target)),
            SwitchInt {
                discr,
                switch_ty: _,
                targets,
            } => {
                let temp_1 = TemporaryPlace { id: 1 };
                let temp_1_mut = self.encode_operand(current, discr, temp_1)?;
                Ok(MicroMirTerminator::JumpInt(
                    temp_1.into(),
                    targets.iter().collect(),
                    temp_1_mut,
                ))
            }
            Abort => Ok(MicroMirTerminator::FailVerif),
            Unreachable => Ok(MicroMirTerminator::FailVerif),
            Return => {
                let return_mutability =
                    self.lookup_place_mutability(&Local::from_usize(0).into(), &self.body)?;
                Ok(MicroMirTerminator::Return(return_mutability))
            }
            Drop {
                place,
                target,
                unwind: _,
            } => {
                current.push(MicroMirStatement::Kill((*place).into()));
                Ok(MicroMirTerminator::Jump(*target))
            }
            DropAndReplace {
                place,
                value,
                target,
                unwind: _,
            } => {
                self.encode_assign_use(current, place, value)?;
                Ok(MicroMirTerminator::Jump(*target))
            }
            us => Err(MicroMirEncodingError::UnsupportedStatementError(format!(
                "Unimplemented statement {:#?}",
                us
            ))),
        }
    }

    fn encode_assign_use(
        &self,
        current: &mut Vec<MicroMirStatement<'tcx>>,
        p_dest: &Place<'tcx>,
        op: &Operand<'tcx>,
    ) -> Result<(), MicroMirEncodingError> {
        // 1. Kill p_dest
        // 2. Encode operand
        // 3. Set pl with temp1's mutability
        current.push(MicroMirStatement::Kill((*p_dest).into()));
        let temp_1 = TemporaryPlace { id: 1 };

        // TODO: monad
        match self.encode_operand(current, op, temp_1) {
            Ok(temp1_mut) => {
                current.push(MicroMirStatement::Set(temp_1, *p_dest, temp1_mut));
                return Ok(());
            }
            Err(e) => return Err(e),
        }
    }

    fn encode_assign_len(
        &self,
        current: &mut Vec<MicroMirStatement<'tcx>>,
        p_dest: &Place<'tcx>,
        p0: &Place<'tcx>,
    ) -> Result<(), MicroMirEncodingError> {
        // 1. Kill p_dest
        // 2. Compute len into temp
        // 3. Assign p_dest, with owning permission
        current.push(MicroMirStatement::Kill((*p_dest).into()));
        let p0_mut = self.lookup_place_mutability(&p0, self.body)?;
        let temp_1 = TemporaryPlace { id: 1 };
        current.push(MicroMirStatement::Len(*p0, temp_1, p0_mut));
        current.push(MicroMirStatement::Set(temp_1, *p_dest, Mut));
        return Ok(());
    }

    fn encode_nullop(
        &self,
        current: &mut Vec<MicroMirStatement<'tcx>>,
        nullop: NullOp,
        p_dest: &Place<'tcx>,
    ) -> Result<(), MicroMirEncodingError> {
        // 1. Kill p_dest
        // 2. Encode UnOp statement
        current.push(MicroMirStatement::Kill((*p_dest).into()));
        let temp_1 = TemporaryPlace { id: 1 };
        current.push(MicroMirStatement::NullOp(nullop, temp_1));
        current.push(MicroMirStatement::Set(temp_1, *p_dest, Mut));
        return Ok(());
    }

    fn encode_unop(
        &self,
        current: &mut Vec<MicroMirStatement<'tcx>>,
        unop: UnOp,
        op1: &Operand<'tcx>,
        p_dest: &Place<'tcx>,
    ) -> Result<(), MicroMirEncodingError> {
        // 1. Kill p_dest
        // 2. Encode first operand into temporary
        // 3. Encode UnOp statement
        // Note: Binop always gets exclusive permission out of it's operands, usually by a copy.
        current.push(MicroMirStatement::Kill((*p_dest).into()));
        let temp_1 = TemporaryPlace { id: 1 };
        let temp_2 = TemporaryPlace { id: 2 };
        if let Ok(Mut) = self.encode_operand(current, op1, temp_1) {
            // This has no effect for now, it's assumed temp_1 is mutable.
        } else {
            return Err(MicroMirEncodingError::ExpectedMutableError(format!(
                "Expected operand {:#?} to be mutable",
                op1
            )));
        }

        current.push(MicroMirStatement::UnOp(unop, temp_1, temp_2));
        current.push(MicroMirStatement::Set(temp_2, *p_dest, Mut));
        return Ok(());
    }

    fn encode_binop(
        &self,
        current: &mut Vec<MicroMirStatement<'tcx>>,
        binop: BinOp,
        op1: &Operand<'tcx>,
        op2: &Operand<'tcx>,
        p_dest: &Place<'tcx>,
        is_checked: bool,
    ) -> Result<(), MicroMirEncodingError> {
        // 1. Kill p_dest
        // 2. Encode first operand into temporary
        // 3. Encode next operand into temporary
        // 4. Encode BinOp statement
        // Note: Binop always gets exclusive permission out of it's operands, usually by a copy.
        current.push(MicroMirStatement::Kill((*p_dest).into()));
        let temp_1 = TemporaryPlace { id: 1 };
        let temp_2 = TemporaryPlace { id: 2 };
        let temp_3 = TemporaryPlace { id: 3 };
        if let Ok(Mut) = self.encode_operand(current, op1, temp_1) {
            // This has no effect for now, it's assumed temp_1 is mutable.
        } else {
            return Err(MicroMirEncodingError::ExpectedMutableError(format!(
                "Expected operand {:#?} to be mutable",
                op1
            )));
        }
        if let Ok(Mut) = self.encode_operand(current, op2, temp_2) {
            // This has no effect for now, it's assumed temp_2 is mutable.
        } else {
            return Err(MicroMirEncodingError::ExpectedMutableError(format!(
                "Expected operand {:#?} to be mutable",
                op2
            )));
        }
        current.push(MicroMirStatement::BinaryOp(
            binop, is_checked, temp_1, temp_2, temp_3,
        ));
        current.push(MicroMirStatement::Set(temp_3, *p_dest, Mut));
        return Ok(());
    }

    /// Appends the encoding which constructs a temporary from an operand to a current MicroMir block.
    /// Returns the mutability it decides the temporary should have... however non-mutable operands
    /// have no use yet.
    /// Eventually they will, for example in the Repeat Rvalue.
    fn encode_operand(
        &self,
        current: &mut Vec<MicroMirStatement<'tcx>>,
        op: &Operand<'tcx>,
        into: TemporaryPlace,
    ) -> Result<Mutability, MicroMirEncodingError> {
        match op {
            Copy(p) => {
                let p_mut = self.lookup_place_mutability(&p, self.body)?;
                current.push(MicroMirStatement::Duplicate(p.clone(), into, p_mut));
                return Ok(p_mut);
            }
            Move(p) => {
                current.push(MicroMirStatement::Move(p.clone(), into));
                return Ok(Mut);
            }
            Constant(box k) => {
                current.push(MicroMirStatement::Constant(*k, into));
                return Ok(Mut);
            }
        }
    }

    fn lookup_place_mutability(
        &self,
        p: &Place<'tcx>,
        body: &Body,
    ) -> Result<Mutability, MicroMirEncodingError> {
        if let Some(localdecl) = body.local_decls.get(p.local) {
            match localdecl.ty.kind() {
                ty::TyKind::Ref(_, _, m) => return Ok(*m),
                err_t => {
                    return Err(MicroMirEncodingError::LocalError(format!(
                        "Expected refrerence {:#?} has type {:#?}",
                        p.local, err_t
                    )));
                }
            }
        } else {
            return Err(MicroMirEncodingError::LocalError(format!(
                "Could not get local_decls for local {:#?}",
                p.local
            )));
        }
    }
}
