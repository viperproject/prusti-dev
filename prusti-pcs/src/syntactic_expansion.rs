// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![allow(dead_code)]

use crate::pcs::{MicroMirStatement, Mutability, TemporaryPlace};
use rustc_middle::mir::{
    BinOp, NullOp, Operand, Operand::*, Place, Rvalue::*, Statement, StatementKind::*, UnOp,
};

/// Appends the encoding which performs (our operational interpretation of) a MIR statement
/// to a current MicroMir block.
///
/// TODO: For now I only have temporaries with exclusive permissions. Is this always the case?
fn encode_individual_statement<'tcx>(
    current: &mut Vec<MicroMirStatement<'tcx>>,
    s: &Statement<'tcx>,
) -> Result<(), ()> {
    match &s.kind {
        Assign(box (p_dest, Use(op))) => {
            // 1. Kill p_dest
            // 2. Encode operand
            // 3. Set pl with temp1's mutability
            current.push(MicroMirStatement::Kill((*p_dest).into()));
            let temp_1 = TemporaryPlace { id: 1 };
            if let Ok(temp1_mut) = encode_operand(current, op, temp_1) {
                current.push(MicroMirStatement::Set(temp_1, *p_dest, temp1_mut));
            } else {
                return Err(());
            }
        }

        Assign(box (p_dest, Len(p0))) => {
            // 1. Kill p_dest
            // 2. Compute len into temp
            // 3. Assign p_dest, with owning permission
            current.push(MicroMirStatement::Kill((*p_dest).into()));
            let p0_mut = lookup_place_mutability(&p0);
            let temp_1 = TemporaryPlace { id: 1 };
            current.push(MicroMirStatement::Len(*p0, temp_1, p0_mut));
            current.push(MicroMirStatement::Set(temp_1, *p_dest, Mutability::Mut));
        }

        Assign(box (p_dest, BinaryOp(binop, box (op1, op2)))) => {
            return encode_binop(current, *binop, op1, op2, p_dest, false);
        }

        Assign(box (p_dest, CheckedBinaryOp(binop, box (op1, op2)))) => {
            return encode_binop(current, *binop, op1, op2, p_dest, true);
        }

        Assign(box (p_dest, UnaryOp(unop, op))) => {
            return encode_unop(current, *unop, op, p_dest);
        }

        Assign(box (p_dest, NullaryOp(nullop, _))) => {
            // TODO: The TY field here isn't used... but I think we'll need it when we lower to Viper.
            return encode_nullop(current, *nullop, p_dest);
        }

        _ => return Err(()),
    }
    return Ok(());
}

fn encode_nullop<'tcx>(
    current: &mut Vec<MicroMirStatement<'tcx>>,
    nullop: NullOp,
    p_dest: &Place<'tcx>,
) -> Result<(), ()> {
    // 1. Kill p_dest
    // 2. Encode UnOp statement
    current.push(MicroMirStatement::Kill((*p_dest).into()));
    let temp_1 = TemporaryPlace { id: 1 };
    current.push(MicroMirStatement::NullOp(nullop, temp_1));
    current.push(MicroMirStatement::Set(temp_1, *p_dest, Mutability::Mut));
    return Ok(());
}

fn encode_unop<'tcx>(
    current: &mut Vec<MicroMirStatement<'tcx>>,
    unop: UnOp,
    op1: &Operand<'tcx>,
    p_dest: &Place<'tcx>,
) -> Result<(), ()> {
    // 1. Kill p_dest
    // 2. Encode first operand into temporary
    // 3. Encode UnOp statement
    // Note: Binop always gets exclusive permission out of it's operands, usually by a copy.
    current.push(MicroMirStatement::Kill((*p_dest).into()));
    let temp_1 = TemporaryPlace { id: 1 };
    let temp_2 = TemporaryPlace { id: 2 };
    if let Ok(Mutability::Mut) = encode_operand(current, op1, temp_1) {
        // This has no effect for now, it's assumed temp_1 is mutable.
    } else {
        return Err(());
    }

    current.push(MicroMirStatement::UnOp(unop, temp_1, temp_2));
    current.push(MicroMirStatement::Set(temp_2, *p_dest, Mutability::Mut));
    return Ok(());
}

fn encode_binop<'tcx>(
    current: &mut Vec<MicroMirStatement<'tcx>>,
    binop: BinOp,
    op1: &Operand<'tcx>,
    op2: &Operand<'tcx>,
    p_dest: &Place<'tcx>,
    is_checked: bool,
) -> Result<(), ()> {
    // 1. Kill p_dest
    // 2. Encode first operand into temporary
    // 3. Encode next operand into temporary
    // 4. Encode BinOp statement
    // Note: Binop always gets exclusive permission out of it's operands, usually by a copy.
    current.push(MicroMirStatement::Kill((*p_dest).into()));
    let temp_1 = TemporaryPlace { id: 1 };
    let temp_2 = TemporaryPlace { id: 2 };
    let temp_3 = TemporaryPlace { id: 3 };
    if let Ok(Mutability::Mut) = encode_operand(current, op1, temp_1) {
        // This has no effect for now, it's assumed temp_1 is mutable.
    } else {
        return Err(());
    }
    if let Ok(Mutability::Mut) = encode_operand(current, op2, temp_2) {
        // This has no effect for now, it's assumed temp_2 is mutable.
    } else {
        return Err(());
    }
    current.push(MicroMirStatement::BinaryOp(
        binop, is_checked, temp_1, temp_2, temp_3,
    ));
    current.push(MicroMirStatement::Set(temp_3, *p_dest, Mutability::Mut));
    return Ok(());
}

/// Appends the encoding which constructs a temporary from an operand to a current MicroMir block.
/// Returns the mutability it decides the temporary should have... however non-mutable operands
/// have no use yet.
/// Eventually they will, for example in the Repeat Rvalue.
fn encode_operand<'tcx>(
    current: &mut Vec<MicroMirStatement<'tcx>>,
    op: &Operand<'tcx>,
    into: TemporaryPlace,
) -> Result<Mutability, ()> {
    match op {
        Copy(p) => {
            let p_mut = lookup_place_mutability(&p);
            current.push(MicroMirStatement::Duplicate(p.clone(), into, p_mut));
            return Ok(p_mut);
        }
        Move(p) => {
            current.push(MicroMirStatement::Move(p.clone(), into));
            return Ok(Mutability::Mut);
        }
        Constant(box k) => {
            current.push(MicroMirStatement::Constant(*k, into));
            return Ok(Mutability::Mut);
        }
    }
}

fn lookup_place_mutability<'tcx>(_p: &Place<'tcx>) -> Mutability {
    // I see some implementation of this in the current procedure encoder.
    // I know I'll need to pass this more paramaters, but I don't know which yet.
    // Likely, I'll wrap all these top-level functions into a struct with
    // this as a method.
    todo!();
}
