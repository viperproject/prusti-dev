// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![allow(dead_code)]

use crate::pcs::{MicroMirStatement, MicroMirTerminator, TemporaryPlace};

use rustc_middle::{
    mir::{
        terminator::{Terminator, TerminatorKind::*},
        BinOp, Body, Local, Mutability,
        Mutability::*,
        NullOp, Operand,
        Operand::*,
        Place,
        Rvalue::*,
        Statement,
        StatementKind::*,
        UnOp,
    },
    ty,
};

use crate::syntactic_expansion::MicroMirEncodingError::*;

pub enum MicroMirEncodingError {
    UnsupportedStatementError(String),
    ExpectedMutableError(String),
    LocalError(String),
}

/// Intermediate object containing all information for the MIR->Pre-MicroMir translation
pub struct MicroMirEncoder<'mir, 'tcx: 'mir> {
    pub body: &'mir Body<'mir>,
    pub encoding: &'tcx Vec<Vec<MicroMirStatement<'tcx>>>,
}

impl<'mir, 'tcx: 'mir> MicroMirEncoder<'mir, 'tcx> {
    /// Encodes a MIR statement into MicroMir statements
    /// TODO: For now I only have temporaries with exclusive permissions. Is this always the case?
    fn encode_individual_statement(
        &self,
        current: &mut Vec<MicroMirStatement<'tcx>>,
        s: &Statement<'tcx>,
    ) -> Result<(), MicroMirEncodingError> {
        match &s.kind {
            Assign(box (p_dest, Use(op))) => self.encode_assign_use(current, p_dest, op),

            Assign(box (p_dest, Len(p0))) => self.encode_assign_len(current, p_dest, p0),

            Assign(box (p_dest, BinaryOp(binop, box (op1, op2)))) => {
                self.encode_binop(current, *binop, op1, op2, p_dest, false)
            }

            Assign(box (p_dest, CheckedBinaryOp(binop, box (op1, op2)))) => {
                self.encode_binop(current, *binop, op1, op2, p_dest, true)
            }

            Assign(box (p_dest, UnaryOp(unop, op))) => self.encode_unop(current, *unop, op, p_dest),

            // TODO: The "ty" field here isn't used... but I think we'll need it when we lower to Viper.
            Assign(box (p_dest, NullaryOp(nullop, _))) => {
                self.encode_nullop(current, *nullop, p_dest)
            }

            us => Err(UnsupportedStatementError(format!(
                "Unsupported Statement: {:#?}",
                us
            ))),
        }
    }

    /// Encodes a MIR terminator into a MicroMir terminator, potentially adding steps to the body.
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
                    self.lookup_place_mutability(&Local::from_usize(0).into())?;
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

    /// Encodes an assignment with a USE operand
    /// 1. Kill p_dest
    /// 2. Encode operand
    /// 3. Set pl with temp1's mutability
    fn encode_assign_use(
        &self,
        current: &mut Vec<MicroMirStatement<'tcx>>,
        p_dest: &Place<'tcx>,
        op: &Operand<'tcx>,
    ) -> Result<(), MicroMirEncodingError> {
        current.push(MicroMirStatement::Kill((*p_dest).into()));
        let temp_1 = TemporaryPlace { id: 1 };
        let temp1_mut = self.encode_operand(current, op, temp_1)?;
        current.push(MicroMirStatement::Set(temp_1, *p_dest, temp1_mut));
        Ok(())
    }

    /// Encodes an assignment with a USE operand
    /// 1. Kill p_dest
    /// 2. Compute len into temp
    /// 3. Assign p_dest, with owning permission
    fn encode_assign_len(
        &self,
        current: &mut Vec<MicroMirStatement<'tcx>>,
        p_dest: &Place<'tcx>,
        p0: &Place<'tcx>,
    ) -> Result<(), MicroMirEncodingError> {
        current.push(MicroMirStatement::Kill((*p_dest).into()));
        let p0_mut = self.lookup_place_mutability(&p0)?;
        let temp_1 = TemporaryPlace { id: 1 };
        current.push(MicroMirStatement::Len(*p0, temp_1, p0_mut));
        current.push(MicroMirStatement::Set(temp_1, *p_dest, Mut));
        Ok(())
    }

    /// Encodes an assignment with a NullOp operand
    /// 1. Kill p_dest
    /// 2. Encode UnOp statement
    fn encode_nullop(
        &self,
        current: &mut Vec<MicroMirStatement<'tcx>>,
        nullop: NullOp,
        p_dest: &Place<'tcx>,
    ) -> Result<(), MicroMirEncodingError> {
        current.push(MicroMirStatement::Kill((*p_dest).into()));
        let temp_1 = TemporaryPlace { id: 1 };
        current.push(MicroMirStatement::NullOp(nullop, temp_1));
        current.push(MicroMirStatement::Set(temp_1, *p_dest, Mut));
        Ok(())
    }

    /// Encodes an assignment with a UnOp operand
    /// 1. Kill p_dest
    /// 2. Encode first operand into temporary
    /// 3. Encode UnOp statement
    /// Note: Binop always gets exclusive permission out of it's operands, usually by a copy.
    ///       (&u32 + &u32 is not allowed)
    fn encode_unop(
        &self,
        current: &mut Vec<MicroMirStatement<'tcx>>,
        unop: UnOp,
        op1: &Operand<'tcx>,
        p_dest: &Place<'tcx>,
    ) -> Result<(), MicroMirEncodingError> {
        current.push(MicroMirStatement::Kill((*p_dest).into()));
        let temp_1 = TemporaryPlace { id: 1 };
        let temp_2 = TemporaryPlace { id: 2 };
        let op_mut = self.encode_operand(current, op1, temp_1)?;
        if op_mut != Mut {
            return Err(ExpectedMutableError(format!(
                "Expected operand {:#?} to be mutable",
                op1
            )));
        }
        current.push(MicroMirStatement::UnOp(unop, temp_1, temp_2));
        current.push(MicroMirStatement::Set(temp_2, *p_dest, Mut));
        Ok(())
    }

    /// Encodes an assignment with a BinOp operand
    /// 1. Kill p_dest
    /// 2. Encode first operand into temporary
    /// 3. Encode next operand into temporary
    /// 4. Encode BinOp statement
    /// See UnOp note about exclusive permission to operands.
    fn encode_binop(
        &self,
        current: &mut Vec<MicroMirStatement<'tcx>>,
        binop: BinOp,
        op1: &Operand<'tcx>,
        op2: &Operand<'tcx>,
        p_dest: &Place<'tcx>,
        is_checked: bool,
    ) -> Result<(), MicroMirEncodingError> {
        current.push(MicroMirStatement::Kill((*p_dest).into()));
        let temp_1 = TemporaryPlace { id: 1 };
        let temp_2 = TemporaryPlace { id: 2 };
        let temp_3 = TemporaryPlace { id: 3 };
        let op_mut_1 = self.encode_operand(current, op1, temp_1)?;
        if op_mut_1 != Mut {
            return Err(MicroMirEncodingError::ExpectedMutableError(format!(
                "Expected operand {:#?} to be mutable",
                op1
            )));
        }
        let op_mut_2 = self.encode_operand(current, op2, temp_2)?;
        if op_mut_2 != Mut {
            return Err(MicroMirEncodingError::ExpectedMutableError(format!(
                "Expected operand {:#?} to be mutable",
                op2
            )));
        }
        current.push(MicroMirStatement::BinaryOp(
            binop, is_checked, temp_1, temp_2, temp_3,
        ));
        current.push(MicroMirStatement::Set(temp_3, *p_dest, Mut));
        Ok(())
    }

    /// Appends the encoding which constructs a temporary from an operand to a current MicroMir block.
    /// Returns the mutability it decides the temporary should have
    /// TODO: Currently, all operands give exclusive permission, but this will not always be the case.
    fn encode_operand(
        &self,
        current: &mut Vec<MicroMirStatement<'tcx>>,
        op: &Operand<'tcx>,
        into: TemporaryPlace,
    ) -> Result<Mutability, MicroMirEncodingError> {
        match op {
            Copy(p) => {
                let p_mut = self.lookup_place_mutability(&p)?;
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

    /// Accesses a place's mutability from the current MIR body.
    fn lookup_place_mutability(
        &self,
        p: &Place<'tcx>,
    ) -> Result<Mutability, MicroMirEncodingError> {
        if let Some(localdecl) = self.body.local_decls.get(p.local) {
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
