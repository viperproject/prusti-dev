// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![allow(dead_code)]
use crate::{
    syntax::{
        hoare_semantics::*,
        micromir::{
            LinearResource, MicroMirData, MicroMirStatement, MicroMirTerminator, PCSPermission,
            TemporaryPlace, PCS,
        },
    },
    util::EncodingResult,
};
use prusti_interface::{environment::polonius_info::PoloniusInfo, PrustiError};
use prusti_rustc_interface::{
    data_structures::fx::FxHashMap,
    errors::MultiSpan,
    middle::{
        mir::{
            AggregateKind::Adt, BasicBlock, BinOp, Body, BorrowKind, Local, Location, Mutability,
            Mutability::*, NullOp, Operand, Operand::*, Place, Rvalue::*, Statement,
            StatementKind::*, Terminator, TerminatorKind::*, UnOp,
        },
        ty,
        ty::TyCtxt,
    },
};

/// Basic block context, intermidiate state of a basic block
struct BBCtx<'mir, 'tcx: 'mir> {
    mir: &'mir Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    stmt_idx: usize,
    statements: Vec<MicroMirStatement<'tcx>>,
    parents: Vec<usize>,
    block: BasicBlock,
}

impl<'mir, 'tcx: 'mir> BBCtx<'mir, 'tcx> {
    pub fn new(block: BasicBlock, mir: &'mir Body<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        BBCtx {
            mir,
            tcx,
            stmt_idx: 0,
            statements: Vec::default(),
            parents: Vec::default(),
            block,
        }
    }

    pub fn set_stmt_idx(&mut self, i: usize) {
        self.stmt_idx = i;
    }

    pub fn push_stmt(&mut self, stmt: MicroMirStatement<'tcx>) {
        self.statements.push(stmt);
        self.parents.push(self.stmt_idx);
    }

    pub fn mir(&self) -> &'mir Body<'tcx> {
        self.mir
    }

    pub fn finalize(&self, term: MicroMirTerminator<'tcx>) -> MicroMirData<'tcx> {
        // TODO: How to move out this data... external function not in impl? destructor?
        MicroMirData {
            statements: self.statements.clone(),
            terminator: term,
            mir_parent: self.parents.clone(),
            mir_block: self.block,
        }
    }
}

pub type MicroMirEncoding<'tcx> = FxHashMap<BasicBlock, MicroMirData<'tcx>>;

/// Intermediate object containing all information for the MIR->Pre-MicroMir translation
pub struct MicroMirEncoder<'mir, 'tcx: 'mir> {
    pub encoding: MicroMirEncoding<'tcx>,
    pub mir: &'mir Body<'tcx>,
}

impl<'mir, 'tcx: 'mir> MicroMirEncoder<'mir, 'tcx> {
    pub fn expand_syntax(mir: &'mir Body<'tcx>, tcx: TyCtxt<'tcx>) -> EncodingResult<Self> {
        let mut encoding: FxHashMap<BasicBlock, MicroMirData<'tcx>> = FxHashMap::default();
        for (bb, bbdata) in mir.basic_blocks.iter_enumerated() {
            let mut ctx: BBCtx<'mir, 'tcx> = BBCtx::new(bb, &mir, tcx);
            // let mut statements: Vec<MicroMirStatement<'tcx>> = vec![];
            for (stmt_idx, statement) in bbdata.statements.iter().enumerate() {
                ctx.set_stmt_idx(stmt_idx);
                Self::encode_individual_statement(&mut ctx, statement)?;
            }
            let terminator = Self::encode_terminator(&mut ctx, bbdata.terminator())?;
            // let current_block_data = MicroMirData {
            //     statements,
            //     terminator,
            // };
            encoding.insert(bb, ctx.finalize(terminator));
        }
        Ok(Self { encoding, mir })
    }

    /// Encodes a MIR statement into MicroMir statements
    /// TODO: For now I only have temporaries with exclusive permissions. Is this always the case?
    fn encode_individual_statement(
        ctx: &mut BBCtx<'mir, 'tcx>,
        s: &Statement<'tcx>,
    ) -> EncodingResult<()> {
        match &s.kind {
            Assign(box (p_dest, Use(op))) => Self::encode_assign_use(ctx, p_dest, op),

            Assign(box (p_dest, Len(p0))) => Self::encode_assign_len(ctx, p_dest, p0),

            Assign(box (p_dest, BinaryOp(binop, box (op1, op2)))) => {
                Self::encode_binop(ctx, *binop, op1, op2, p_dest, false)
            }

            Assign(box (p_dest, CheckedBinaryOp(binop, box (op1, op2)))) => {
                Self::encode_binop(ctx, *binop, op1, op2, p_dest, true)
            }

            Assign(box (p_dest, UnaryOp(unop, op))) => Self::encode_unop(ctx, *unop, op, p_dest),

            // TODO: The "ty" field here isn't used... but I think we'll need it when we lower to Viper.
            Assign(box (p_dest, NullaryOp(nullop, _))) => Self::encode_nullop(ctx, *nullop, p_dest),

            Assign(box (
                p_from,
                Ref(
                    _,
                    BorrowKind::Mut {
                        allow_two_phase_borrow: _,
                    },
                    p_to,
                ),
            )) => Self::encode_borrow(ctx, *p_from, *p_to),

            // TODO: These need to be discussed
            StorageDead(local) => Self::encode_storagedead(ctx, *local),

            // TODO: These need to be discussed
            StorageLive(local) => Self::encode_storagelive(ctx, *local),

            // TODO: These need to be discussed
            Assign(box (dest, Aggregate(box Adt(_, _, _, _, _), operands))) => {
                Self::encode_aggregate(ctx, dest, operands)
            }

            FakeRead(box (_, _)) => Ok(()),

            AscribeUserType(box (_p, _proj), _variance) => Ok(()),

            us => Err(PrustiError::unsupported(
                format!("unsupported statement: {:#?}", us),
                MultiSpan::new(),
            )),
        }
    }

    /// Encodes a MIR terminator into a MicroMir terminator, potentially adding steps to the body.
    fn encode_terminator(
        ctx: &mut BBCtx<'mir, 'tcx>,
        t: &'mir Terminator<'tcx>,
    ) -> EncodingResult<MicroMirTerminator<'tcx>> {
        match &t.kind {
            Goto { target } => Ok(MicroMirTerminator::Jump(*target)),

            SwitchInt {
                discr,
                targets,
                ..
            } => {
                let temp_1 = TemporaryPlace { id: 1 };
                let temp_1_mut = Self::encode_operand(ctx, discr, temp_1)?;

                let mut next_targets: Vec<(Option<u128>, BasicBlock)> =
                    targets.iter().map(|(v, bb)| (Some(v), bb)).collect();
                next_targets.push((None, targets.otherwise()));

                Ok(MicroMirTerminator::JumpInt(
                    temp_1.into(),
                    next_targets,
                    temp_1_mut,
                ))
            }

            Abort => Ok(MicroMirTerminator::FailVerif),

            Unreachable => Ok(MicroMirTerminator::FailVerif),

            Return => {
                let _return_mutability =
                    Self::lookup_place_mutability(&Local::from_usize(0).into(), ctx.mir())?;
                Ok(MicroMirTerminator::Return())
            }

            Drop {
                place,
                target,
                unwind: _,
            } => {
                ctx.push_stmt(MicroMirStatement::Kill(None, (*place).into()));
                Ok(MicroMirTerminator::Jump(*target))
            }

            DropAndReplace {
                place,
                value,
                target,
                unwind: _,
            } => {
                Self::encode_assign_use(ctx, place, value)?;
                Ok(MicroMirTerminator::Jump(*target))
            }

            FalseUnwind {
                real_target,
                unwind: _,
            } => Ok(MicroMirTerminator::Jump(*real_target)),

            // TODO: This is wrong, but is a patch until I get DFS/BFS translation
            Resume => Ok(MicroMirTerminator::FailVerif),

            Assert {
                cond,
                expected: _,
                msg: _,
                target,
                cleanup: _,
            } => {
                let temp_1 = TemporaryPlace { id: 1 };
                let _ = Self::encode_operand(ctx, cond, temp_1)?;
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
    fn encode_assign_use(
        ctx: &mut BBCtx<'mir, 'tcx>,
        p_dest: &Place<'tcx>,
        op: &Operand<'tcx>,
    ) -> EncodingResult<()> {
        if p_dest.ty(&ctx.mir.local_decls, ctx.tcx).ty.is_ref() {
            match op {
                Copy(_) | Constant(_) => todo!(),
                Move(p_from) => {
                    // ctx.push_stmt(MicroMirStatement::Kill(None, (*p_dest).into()));
                    ctx.push_stmt(MicroMirStatement::BorrowMove(
                        (*p_from).clone(),
                        (*p_dest).clone(),
                    ));
                    return Ok(());
                }
            }
        }
        ctx.push_stmt(MicroMirStatement::Kill(None, (*p_dest).into()));
        let temp_1 = TemporaryPlace { id: 1 };
        let temp1_mut = Self::encode_operand(ctx, op, temp_1)?;
        ctx.push_stmt(MicroMirStatement::Set(temp_1, *p_dest, temp1_mut));
        Ok(())
    }

    /// Encodes an assignment with a USE operand
    /// 1. Kill p_dest
    /// 2. Compute len into temp
    /// 3. Assign p_dest, with owning permission
    fn encode_assign_len(
        ctx: &mut BBCtx<'mir, 'tcx>,
        p_dest: &Place<'tcx>,
        p0: &Place<'tcx>,
    ) -> EncodingResult<()> {
        ctx.push_stmt(MicroMirStatement::Kill(None, (*p_dest).into()));
        let p0_mut = Self::lookup_place_mutability(&p0, ctx.mir())?;
        let temp_1 = TemporaryPlace { id: 1 };
        ctx.push_stmt(MicroMirStatement::Len(*p0, temp_1, p0_mut));
        ctx.push_stmt(MicroMirStatement::Set(temp_1, *p_dest, Mut));
        Ok(())
    }

    /// Encodes an assignment with a NullOp operand
    /// 1. Kill p_dest
    /// 2. Encode UnOp statement
    fn encode_nullop(
        ctx: &mut BBCtx<'mir, 'tcx>,
        nullop: NullOp,
        p_dest: &Place<'tcx>,
    ) -> EncodingResult<()> {
        ctx.push_stmt(MicroMirStatement::Kill(None, (*p_dest).into()));
        let temp_1 = TemporaryPlace { id: 1 };
        ctx.push_stmt(MicroMirStatement::NullOp(nullop, temp_1));
        ctx.push_stmt(MicroMirStatement::Set(temp_1, *p_dest, Mut));
        Ok(())
    }

    /// Encodes an assignment with a UnOp operand?
    /// 1. Kill p_dest
    /// 2. Encode first operand into temporary
    /// 3. Encode UnOp statement
    /// Note: Binop always gets exclusive permission out of it's operands, usually by a copy.
    ///       (&u32 + &u32 is not allowed)
    fn encode_unop(
        ctx: &mut BBCtx<'mir, 'tcx>,
        unop: UnOp,
        op1: &Operand<'tcx>,
        p_dest: &Place<'tcx>,
    ) -> EncodingResult<()> {
        ctx.push_stmt(MicroMirStatement::Kill(None, (*p_dest).into()));
        let temp_1 = TemporaryPlace { id: 1 };
        let temp_2 = TemporaryPlace { id: 2 };
        let op_mut = Self::encode_operand(ctx, op1, temp_1)?;
        if op_mut != Mut {
            return Err(PrustiError::internal(
                format!("expected operand {:#?} to be mutable", op1),
                MultiSpan::new(),
            ));
        }
        ctx.push_stmt(MicroMirStatement::UnOp(unop, temp_1, temp_2));
        ctx.push_stmt(MicroMirStatement::Set(temp_2, *p_dest, Mut));
        Ok(())
    }

    /// Encodes an assignment with a BinOp operand
    /// 1. Kill p_dest
    /// 2. Encode first operand into temporary
    /// 3. Encode next operand into temporary
    /// 4. Encode BinOp statement
    /// See UnOp note about exclusive permission to operands.
    fn encode_binop(
        ctx: &mut BBCtx<'mir, 'tcx>,
        binop: BinOp,
        op1: &Operand<'tcx>,
        op2: &Operand<'tcx>,
        p_dest: &Place<'tcx>,
        is_checked: bool,
    ) -> EncodingResult<()> {
        ctx.push_stmt(MicroMirStatement::Kill(None, (*p_dest).into()));
        let temp_1 = TemporaryPlace { id: 1 };
        let temp_2 = TemporaryPlace { id: 2 };
        let temp_3 = TemporaryPlace { id: 3 };
        let op_mut_1 = Self::encode_operand(ctx, op1, temp_1)?;
        if op_mut_1 != Mut {
            return Err(PrustiError::internal(
                format!("expected operand {:#?} to be mutable", op2),
                MultiSpan::new(),
            ));
        }
        let op_mut_2 = Self::encode_operand(ctx, op2, temp_2)?;
        if op_mut_2 != Mut {
            return Err(PrustiError::internal(
                format!("expected operand {:#?} to be mutable", op2),
                MultiSpan::new(),
            ));
        }
        ctx.push_stmt(MicroMirStatement::BinaryOp(
            binop, is_checked, temp_1, temp_2, temp_3,
        ));
        ctx.push_stmt(MicroMirStatement::Set(temp_3, *p_dest, Mut));
        Ok(())
    }

    /// Appends the encoding which constructs a temporary from an operand to a current MicroMir block.
    /// Returns the mutability it decides the temporary should have
    /// TODO: Currently, all operands give exclusive permission, but this will not always be the case.
    fn encode_operand(
        ctx: &mut BBCtx<'mir, 'tcx>,
        op: &Operand<'tcx>,
        into: TemporaryPlace,
    ) -> EncodingResult<Mutability> {
        match op {
            Copy(p) => {
                let p_mut = Self::lookup_place_mutability(&p, ctx.mir())?;
                ctx.push_stmt(MicroMirStatement::Duplicate(p.clone(), into, p_mut));
                return Ok(p_mut);
            }
            Move(p) => {
                ctx.push_stmt(MicroMirStatement::Move(p.clone(), into));
                return Ok(Mut);
            }
            Constant(box k) => {
                ctx.push_stmt(MicroMirStatement::Constant(*k, into));
                return Ok(Mut);
            }
        }
    }

    /// 1. Kill dest
    /// 2. Encode all operands
    /// 3. Encode a pack from the encoded operands
    /// 4. Set the packed place to a temporary (?)
    fn encode_aggregate(
        ctx: &mut BBCtx<'mir, 'tcx>,
        p_dest: &Place<'tcx>,
        operands: &Vec<Operand<'tcx>>,
    ) -> EncodingResult<()> {
        ctx.push_stmt(MicroMirStatement::Kill(None, (*p_dest).into()));
        let mut to_aggregate: Vec<PCSPermission<'tcx>> = vec![];
        let mut i: usize = 1;
        for op in operands.iter() {
            let temp = TemporaryPlace { id: i };
            let op_mut = Self::encode_operand(ctx, op, temp)?;
            to_aggregate.push(PCSPermission::new_initialized(
                op_mut,
                LinearResource::Tmp(temp),
            ));
            i += 1;
        }
        ctx.push_stmt(MicroMirStatement::Aggregate(
            (*p_dest).into(),
            to_aggregate,
            Mutability::Mut,
        ));
        Ok(())
    }

    // Appends the encoding for a StorageLive
    fn encode_storagelive(ctx: &mut BBCtx<'mir, 'tcx>, l: Local) -> EncodingResult<()> {
        ctx.push_stmt(MicroMirStatement::Allocate(l.into()));
        Ok(())
    }

    // Appends the encoding for a StorageDead
    fn encode_storagedead(ctx: &mut BBCtx<'mir, 'tcx>, l: Local) -> EncodingResult<()> {
        let p: Place<'tcx> = (l.clone()).into();
        ctx.push_stmt(MicroMirStatement::Kill(None, LinearResource::Mir(p)));
        ctx.push_stmt(MicroMirStatement::Deallocate(l.into()));
        Ok(())
    }

    fn encode_borrow(
        ctx: &mut BBCtx<'mir, 'tcx>,
        p_from: Place<'tcx>,
        p_to: Place<'tcx>,
    ) -> EncodingResult<()> {
        ctx.push_stmt(MicroMirStatement::BorrowMut(p_from, p_to));
        Ok(())
    }

    /// Accesses a place's mutability from the current MIR body.
    fn lookup_place_mutability(
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
        for (block, dat) in self.encoding.iter() {
            println!(" ===================== {:?} ===================== ", block);
            for (statement_index, stmt) in dat.statements.iter().enumerate() {
                let mir_loc = Location {
                    block: *block,
                    statement_index: dat.mir_parent[statement_index],
                };

                print!("\t,----------------------------- ");
                Self::pprint_pcs(&stmt.precondition());
                println!("\t| @{:?}", mir_loc);
                println!("\t|  from {:?}", self.mir.stmt_at(mir_loc));
                println!("\t| {:?}", stmt);
                print!("\t'----------------------------- ");
                Self::pprint_pcs(&stmt.postcondition());
            }

            print!("\t,----------------------------- ");
            Self::pprint_pcs(&Some(dat.terminator.precondition()));
            println!("\t| {:?}", dat.terminator);
            Self::pprint_term(&dat.terminator.postcondition());

            println!();
            println!();
        }
    }

    fn pprint_pcs(pcs: &Option<PCS<'tcx>>) {
        match pcs {
            Some(pcs1) => println!("{:?}", pcs1.free),
            None => println!("None"),
        }
    }

    fn pprint_term(jumps: &Vec<(BasicBlock, PCS<'tcx>)>) {
        for (bb, pcs) in jumps {
            println!("\t| => {:?} -> {:?}", bb, pcs.free)
        }
    }
}
