// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![allow(dead_code)]
use crate::{
    syntax::{
        hoare_semantics::*,
        micromir::{MicroMirData, MicroMirStatement, MicroMirTerminator, TemporaryPlace, PCS},
    },
    util::EncodingResult,
};
use prusti_interface::PrustiError;
use prusti_rustc_interface::{
    data_structures::stable_map::FxHashMap,
    errors::MultiSpan,
    middle::{
        mir::{
            AggregateKind::Adt, BasicBlock, BinOp, Body, Local, Mutability, Mutability::*, NullOp,
            Operand, Operand::*, Place, Rvalue::*, Statement, StatementKind::*, Terminator,
            TerminatorKind::*, UnOp,
        },
        ty,
    },
};
/// Intermediate object containing all information for the MIR->Pre-MicroMir translation
pub struct MicroMirEncoder<'tcx> {
    pub encoding: FxHashMap<BasicBlock, MicroMirData<'tcx>>,
}

impl<'tcx> MicroMirEncoder<'tcx> {
    pub fn expand_syntax<'mir>(mir: &'mir Body<'tcx>) -> EncodingResult<Self>
    where
        'tcx: 'mir,
    {
        let mut encoding: FxHashMap<BasicBlock, MicroMirData<'tcx>> = FxHashMap::default();
        for (bb, bbdata) in mir.basic_blocks().iter_enumerated() {
            let mut statements: Vec<MicroMirStatement<'tcx>> = vec![];
            for stmt in bbdata.statements.iter() {
                Self::encode_individual_statement(&mut statements, stmt, mir)?;
            }
            let terminator = Self::encode_terminator(&mut statements, bbdata.terminator(), mir)?;
            let current_block_data = MicroMirData {
                statements,
                terminator,
            };
            encoding.insert(bb, current_block_data);
        }
        Ok(Self { encoding })
    }

    /// Encodes a MIR statement into MicroMir statements
    /// TODO: For now I only have temporaries with exclusive permissions. Is this always the case?
    fn encode_individual_statement<'mir>(
        current: &mut Vec<MicroMirStatement<'tcx>>,
        s: &Statement<'tcx>,
        mir: &'mir Body<'tcx>,
    ) -> EncodingResult<()>
    where
        'tcx: 'mir,
    {
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

            us => Err(PrustiError::unsupported(
                format!("unsupported statement: {:#?}", us),
                MultiSpan::new(),
            )),
        }
    }

    /// Encodes a MIR terminator into a MicroMir terminator, potentially adding steps to the body.
    pub fn encode_terminator<'mir>(
        current: &mut Vec<MicroMirStatement<'tcx>>,
        t: &'mir Terminator<'tcx>,
        mir: &'mir Body<'tcx>,
    ) -> EncodingResult<MicroMirTerminator<'tcx>>
    where
        'tcx: 'mir,
    {
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

            us => Err(PrustiError::unsupported(
                format!("untranslated terminator {:#?}", us),
                MultiSpan::new(),
            )),
        }
    }

    /// Encodes an assignment with a USE operand
    /// 1. Kill p_dest
    /// 2. Encode operand
    /// 3. Set pl with temp1's mutability
    fn encode_assign_use<'mir>(
        current: &mut Vec<MicroMirStatement<'tcx>>,
        p_dest: &Place<'tcx>,
        op: &Operand<'tcx>,
        mir: &'mir Body<'tcx>,
    ) -> EncodingResult<()>
    where
        'tcx: 'mir,
    {
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
    fn encode_assign_len<'mir>(
        current: &mut Vec<MicroMirStatement<'tcx>>,
        p_dest: &Place<'tcx>,
        p0: &Place<'tcx>,
        mir: &'mir Body<'tcx>,
    ) -> EncodingResult<()>
    where
        'tcx: 'mir,
    {
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
        current: &mut Vec<MicroMirStatement<'tcx>>,
        nullop: NullOp,
        p_dest: &Place<'tcx>,
    ) -> EncodingResult<()> {
        current.push(MicroMirStatement::Kill((*p_dest).into()));
        let temp_1 = TemporaryPlace { id: 1 };
        current.push(MicroMirStatement::NullOp(nullop, temp_1));
        current.push(MicroMirStatement::Set(temp_1, *p_dest, Mut));
        Ok(())
    }

    /// Encodes an assignment with a UnOp operand?
    /// 1. Kill p_dest
    /// 2. Encode first operand into temporary
    /// 3. Encode UnOp statement
    /// Note: Binop always gets exclusive permission out of it's operands, usually by a copy.
    ///       (&u32 + &u32 is not allowed)
    fn encode_unop<'mir>(
        current: &mut Vec<MicroMirStatement<'tcx>>,
        unop: UnOp,
        op1: &Operand<'tcx>,
        p_dest: &Place<'tcx>,
        mir: &'mir Body<'tcx>,
    ) -> EncodingResult<()>
    where
        'tcx: 'mir,
    {
        current.push(MicroMirStatement::Kill((*p_dest).into()));
        let temp_1 = TemporaryPlace { id: 1 };
        let temp_2 = TemporaryPlace { id: 2 };
        let op_mut = Self::encode_operand(current, op1, temp_1, mir)?;
        if op_mut != Mut {
            return Err(PrustiError::internal(
                format!("expected operand {:#?} to be mutable", op1),
                MultiSpan::new(),
            ));
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
    fn encode_binop<'mir>(
        current: &mut Vec<MicroMirStatement<'tcx>>,
        binop: BinOp,
        op1: &Operand<'tcx>,
        op2: &Operand<'tcx>,
        p_dest: &Place<'tcx>,
        is_checked: bool,
        mir: &'mir Body<'tcx>,
    ) -> EncodingResult<()>
    where
        'tcx: 'mir,
    {
        current.push(MicroMirStatement::Kill((*p_dest).into()));
        let temp_1 = TemporaryPlace { id: 1 };
        let temp_2 = TemporaryPlace { id: 2 };
        let temp_3 = TemporaryPlace { id: 3 };
        let op_mut_1 = Self::encode_operand(current, op1, temp_1, mir)?;
        if op_mut_1 != Mut {
            return Err(PrustiError::internal(
                format!("expected operand {:#?} to be mutable", op2),
                MultiSpan::new(),
            ));
        }
        let op_mut_2 = Self::encode_operand(current, op2, temp_2, mir)?;
        if op_mut_2 != Mut {
            return Err(PrustiError::internal(
                format!("expected operand {:#?} to be mutable", op2),
                MultiSpan::new(),
            ));
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
    fn encode_operand<'mir>(
        current: &mut Vec<MicroMirStatement<'tcx>>,
        op: &Operand<'tcx>,
        into: TemporaryPlace,
        mir: &'mir Body<'tcx>,
    ) -> EncodingResult<Mutability>
    where
        'tcx: 'mir,
    {
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
    fn encode_storagelive<'mir>(
        current: &mut Vec<MicroMirStatement<'tcx>>,
        l: Local,
        _mir: &'mir Body<'tcx>,
    ) -> EncodingResult<()>
    where
        'tcx: 'mir,
    {
        current.push(MicroMirStatement::Allocate(l.into()));
        Ok(())
    }

    // Appends the encoding for a StorageDead
    fn encode_storagedead<'mir>(
        current: &mut Vec<MicroMirStatement<'tcx>>,
        l: Local,
        _mir: &'mir Body<'tcx>,
    ) -> EncodingResult<()>
    where
        'tcx: 'mir,
    {
        // TODO!!!!
        // current.push(MicroMirStatement::Deallocate(l.into()));
        Ok(())
    }

    /// Accesses a place's mutability from the current MIR body.
    fn lookup_place_mutability<'mir>(
        p: &Place<'tcx>,
        mir: &'mir Body<'tcx>,
    ) -> EncodingResult<Mutability> {
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
            return Err(PrustiError::internal(
                format!("error when retrieving local_decl for local {:#?}", p.local),
                MultiSpan::new(),
            ));
        }
    }

    pub fn get_block(&self, idx: u32) -> EncodingResult<&MicroMirData<'tcx>> {
        match self.encoding.get(&idx.into()) {
            Some(s) => Ok(&s),
            None => Err(PrustiError::internal(
                "unexpected error when retrieving basic block 0",
                MultiSpan::new(),
            )),
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

    fn pprint_pcs(pcs: &Option<PCS<'tcx>>) {
        match pcs {
            Some(pcs1) => println!("{:?}", pcs1.set),
            None => println!("None"),
        }
    }

    fn pprint_term(jumps: &Option<Vec<(BasicBlock, PCS<'tcx>)>>) {
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
