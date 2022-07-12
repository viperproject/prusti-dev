// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![allow(dead_code)]
use crate::pcs::{
    HoareSemantics, MicroMirData, MicroMirStatement, MicroMirTerminator, TemporaryPlace, PCS,
};
use prusti_rustc_interface::{
    data_structures::stable_map::FxHashMap,
    middle::{
        mir::{
            AggregateKind::Adt, BasicBlock, BinOp, Body, Local, Mutability, Mutability::*, NullOp,
            Operand, Operand::*, Place, Rvalue::*, Statement, StatementKind::*, Terminator,
            TerminatorKind::*, UnOp,
        },
        ty,
    },
};

use crate::syntactic_expansion::MicroMirEncodingError::*;

#[derive(Debug)]
pub enum MicroMirEncodingError {
    UnsupportedStatementError(String),
    ExpectedMutableError(String),
    LocalError(String),
}

/// Intermediate object containing all information for the MIR->Pre-MicroMir translation
pub struct MicroMirEncoder<'mir> {
    pub body: &'mir Body<'mir>,
    // The pureley syntactic encoding of the MicroMir, no elaborations yet.
    pub encoding: FxHashMap<BasicBlock, MicroMirData<'mir>>,
    // pub lifetime_endings: FxHashmap<Location,
    // Tranalation of Polonius's
    //      ? origin_contains_loan_at (lifetime contains borrow at)
    //      ? loan_invalidated_at
    //      ? known_contains

    //      loan_live_at (borrow is alive at) => wand can't be applied
}

impl<'mir> MicroMirEncoder<'mir> {
    pub fn expand_syntax(mir: &'mir Body<'mir>) -> Result<Self, MicroMirEncodingError> {
        let mut encoding: FxHashMap<BasicBlock, MicroMirData<'mir>> = FxHashMap::default();
        for (bb, bbdata) in mir.basic_blocks().iter_enumerated() {
            let mut current_block_statements: Vec<MicroMirStatement<'mir>> = vec![];
            for stmt in bbdata.statements.iter() {
                Self::encode_individual_statement(&mut current_block_statements, stmt, mir)?;
            }
            let current_block_terminator =
                Self::encode_terminator(&mut current_block_statements, bbdata.terminator(), mir)?;
            let current_block_data = MicroMirData {
                statements: current_block_statements,
                terminator: current_block_terminator,
            };
            encoding.insert(bb, current_block_data);
        }
        Ok(Self {
            body: mir,
            encoding,
        })
    }

    /// Encodes a MIR statement into MicroMir statements
    /// TODO: For now I only have temporaries with exclusive permissions. Is this always the case?
    fn encode_individual_statement(
        current: &mut Vec<MicroMirStatement<'mir>>,
        s: &Statement<'mir>,
        mir: &Body<'mir>,
    ) -> Result<(), MicroMirEncodingError> {
        match &s.kind {
            Assign(box (p_dest, Use(op))) => Self::encode_assign_use(current, p_dest, op, mir),

            Assign(box (p_dest, Len(p0))) => Self::encode_assign_len(current, p_dest, p0, mir),

            Assign(box (p_dest, BinaryOp(binop, box (op1, op2)))) => {
                Self::encode_binop(current, *binop, op1, op2, p_dest, false, mir)
            }

            Assign(box (p_dest, CheckedBinaryOp(binop, box (op1, op2)))) => {
                Self::encode_binop(current, *binop, op1, op2, p_dest, true, mir)
            }

            Assign(box (p_dest, UnaryOp(unop, op))) => {
                Self::encode_unop(current, *unop, op, p_dest, mir)
            }

            // TODO: The "ty" field here isn't used... but I think we'll need it when we lower to Viper.
            Assign(box (p_dest, NullaryOp(nullop, _))) => {
                Self::encode_nullop(current, *nullop, p_dest)
            }

            // TODO: These need to be discussed
            StorageDead(local) => Self::encode_storagedead(current, *local, mir),

            // TODO: These need to be discussed
            StorageLive(local) => Self::encode_storagelive(current, *local, mir),

            // TODO: These need to be discussed
            Assign(box (_p_dest, Aggregate(box Adt(_, _, _, _, _), _vec))) => Ok(()),

            FakeRead(box (_, _)) => Ok(()),

            AscribeUserType(box (_p, _proj), _variance) => Ok(()),

            us => Err(UnsupportedStatementError(format!(
                "Unsupported Statement: {:?}",
                us
            ))),
        }
    }

    /// Encodes a MIR terminator into a MicroMir terminator, potentially adding steps to the body.
    pub fn encode_terminator(
        current: &mut Vec<MicroMirStatement<'mir>>,
        t: &'mir Terminator<'mir>,
        mir: &Body,
    ) -> Result<MicroMirTerminator<'mir>, MicroMirEncodingError> {
        match &t.kind {
            Goto { target } => Ok(MicroMirTerminator::Jump(*target)),

            SwitchInt {
                discr,
                switch_ty: _,
                targets,
            } => {
                let temp_1 = TemporaryPlace { id: 1 };
                let temp_1_mut = Self::encode_operand(current, discr, temp_1, mir)?;
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
                    Self::lookup_place_mutability(&Local::from_usize(0).into(), mir)?;
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
                Self::encode_assign_use(current, place, value, mir)?;
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
        current: &mut Vec<MicroMirStatement<'mir>>,
        p_dest: &Place<'mir>,
        op: &Operand<'mir>,
        mir: &Body,
    ) -> Result<(), MicroMirEncodingError> {
        current.push(MicroMirStatement::Kill((*p_dest).into()));
        let temp_1 = TemporaryPlace { id: 1 };
        let temp1_mut = Self::encode_operand(current, op, temp_1, mir)?;
        current.push(MicroMirStatement::Set(temp_1, *p_dest, temp1_mut));
        Ok(())
    }

    /// Encodes an assignment with a USE operand
    /// 1. Kill p_dest
    /// 2. Compute len into temp
    /// 3. Assign p_dest, with owning permission
    fn encode_assign_len(
        current: &mut Vec<MicroMirStatement<'mir>>,
        p_dest: &Place<'mir>,
        p0: &Place<'mir>,
        mir: &Body,
    ) -> Result<(), MicroMirEncodingError> {
        current.push(MicroMirStatement::Kill((*p_dest).into()));
        let p0_mut = Self::lookup_place_mutability(&p0, mir)?;
        let temp_1 = TemporaryPlace { id: 1 };
        current.push(MicroMirStatement::Len(*p0, temp_1, p0_mut));
        current.push(MicroMirStatement::Set(temp_1, *p_dest, Mut));
        Ok(())
    }

    /// Encodes an assignment with a NullOp operand
    /// 1. Kill p_dest
    /// 2. Encode UnOp statement
    fn encode_nullop(
        current: &mut Vec<MicroMirStatement<'mir>>,
        nullop: NullOp,
        p_dest: &Place<'mir>,
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
        current: &mut Vec<MicroMirStatement<'mir>>,
        unop: UnOp,
        op1: &Operand<'mir>,
        p_dest: &Place<'mir>,
        mir: &Body,
    ) -> Result<(), MicroMirEncodingError> {
        current.push(MicroMirStatement::Kill((*p_dest).into()));
        let temp_1 = TemporaryPlace { id: 1 };
        let temp_2 = TemporaryPlace { id: 2 };
        let op_mut = Self::encode_operand(current, op1, temp_1, mir)?;
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
        current: &mut Vec<MicroMirStatement<'mir>>,
        binop: BinOp,
        op1: &Operand<'mir>,
        op2: &Operand<'mir>,
        p_dest: &Place<'mir>,
        is_checked: bool,
        mir: &Body,
    ) -> Result<(), MicroMirEncodingError> {
        current.push(MicroMirStatement::Kill((*p_dest).into()));
        let temp_1 = TemporaryPlace { id: 1 };
        let temp_2 = TemporaryPlace { id: 2 };
        let temp_3 = TemporaryPlace { id: 3 };
        let op_mut_1 = Self::encode_operand(current, op1, temp_1, mir)?;
        if op_mut_1 != Mut {
            return Err(MicroMirEncodingError::ExpectedMutableError(format!(
                "Expected operand {:#?} to be mutable",
                op1
            )));
        }
        let op_mut_2 = Self::encode_operand(current, op2, temp_2, mir)?;
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
        current: &mut Vec<MicroMirStatement<'mir>>,
        op: &Operand<'mir>,
        into: TemporaryPlace,
        mir: &Body,
    ) -> Result<Mutability, MicroMirEncodingError> {
        match op {
            Copy(p) => {
                let p_mut = Self::lookup_place_mutability(&p, mir)?;
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

    // Appends the encoding for a StorageLive
    // TODO: StorageLive/StorageDead right now are no-ops. Discuss this.
    fn encode_storagelive(
        current: &mut Vec<MicroMirStatement<'mir>>,
        _l: Local,
        _mir: &Body,
    ) -> Result<(), MicroMirEncodingError> {
        current.push(MicroMirStatement::Nop);
        Ok(())
    }

    // Appends the encoding for a StorageDead
    // TODO: StorageLive/StorageDead right now are no-ops. Discuss this.
    fn encode_storagedead(
        current: &mut Vec<MicroMirStatement<'mir>>,
        _l: Local,
        _mir: &Body,
    ) -> Result<(), MicroMirEncodingError> {
        current.push(MicroMirStatement::Nop);
        Ok(())
    }

    /// Accesses a place's mutability from the current MIR body.
    fn lookup_place_mutability(
        p: &Place<'mir>,
        mir: &Body,
    ) -> Result<Mutability, MicroMirEncodingError> {
        if let Some(localdecl) = mir.local_decls.get(p.local) {
            match localdecl.ty.kind() {
                ty::TyKind::Ref(_, _, m) => return Ok(*m),
                _ => {
                    // If it's not a reference, it has to be owned
                    // TODO: Should owned data be differentiated from &mut data?
                    Ok(Mut)
                }
            }
        } else {
            return Err(MicroMirEncodingError::LocalError(format!(
                "Could not get local_decls for local {:#?}",
                p.local
            )));
        }
    }

    pub fn pprint(&self) {
        let mut current_bb: usize = 0;
        for (_bb, dat) in self.encoding.iter() {
            println!(
                " ===================== {} ===================== ",
                current_bb
            );
            for stmt in dat.statements.iter() {
                print!("\t,----------------------------- ");
                Self::pprint_pcs(&stmt.precondition());
                println!("\t| {:?}", stmt);
                print!("\t'----------------------------- ");
                Self::pprint_pcs(&stmt.postcondition());
            }

            print!("\t,----------------------------- ");
            Self::pprint_pcs(&dat.terminator.precondition());
            println!("\t| {:?}", dat.terminator);
            Self::pprint_term(&dat.terminator.postcondition());

            current_bb += 1;
            println!();
            println!();
        }
    }

    fn pprint_pcs<'tcx>(pcs: &Option<PCS<'tcx>>) {
        match pcs {
            Some(pcs1) => println!("{:?}", pcs1.set),
            None => println!("None"),
        }
    }

    fn pprint_term<'tcx>(jumps: &Option<Vec<(BasicBlock, PCS<'tcx>)>>) {
        match jumps {
            None => println!("\t|\tNone"),
            Some(jumps1) => {
                for (bb, pcs) in jumps1 {
                    println!("\t|\t{:?} -> {:?}", bb, pcs.set)
                }
            }
        }
    }
}
