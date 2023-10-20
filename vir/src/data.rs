use std::fmt::Debug;

use prusti_rustc_interface::middle::mir;
use crate::refs::*;

pub struct LocalData<'vir> {
    pub name: &'vir str, // TODO: identifiers
}

pub struct LocalDeclData<'vir> {
    pub name: &'vir str, // TODO: identifiers
    pub ty: Type<'vir>,
}

#[derive(Clone, Copy, Debug)]
pub enum UnOpKind {
    Neg,
    Not,
}
impl From<mir::UnOp> for UnOpKind {
    fn from(value: mir::UnOp) -> Self {
        match value {
            mir::UnOp::Not => UnOpKind::Not,
            mir::UnOp::Neg => UnOpKind::Neg,
        }
    }
}
impl From<&mir::UnOp> for UnOpKind {
    fn from(value: &mir::UnOp) -> Self {
        UnOpKind::from(*value)
    }
}

#[derive(Clone, Copy, Debug)]
pub enum BinOpKind {
    CmpEq,
    CmpNe,
    CmpGt,
    CmpLt,
    CmpGe,
    CmpLe,
    And,
    Add,
    // ...
}
impl From<mir::BinOp> for BinOpKind {
    fn from(value: mir::BinOp) -> Self {
        match value {
            mir::BinOp::Add => BinOpKind::Add,
            mir::BinOp::AddUnchecked => todo!(),
            mir::BinOp::Sub => todo!(),
            mir::BinOp::SubUnchecked => todo!(),
            mir::BinOp::Mul => todo!(),
            mir::BinOp::MulUnchecked => todo!(),
            mir::BinOp::Div => todo!(),
            mir::BinOp::Rem => todo!(),
            mir::BinOp::BitXor => todo!(),
            mir::BinOp::BitAnd => todo!(),
            mir::BinOp::BitOr => todo!(),
            mir::BinOp::Shl => todo!(),
            mir::BinOp::ShlUnchecked => todo!(),
            mir::BinOp::Shr => todo!(),
            mir::BinOp::ShrUnchecked => todo!(),
            mir::BinOp::Eq => BinOpKind::CmpEq,
            mir::BinOp::Lt => BinOpKind::CmpLt,
            mir::BinOp::Le => BinOpKind::CmpLe,
            mir::BinOp::Ne => BinOpKind::CmpNe,
            mir::BinOp::Ge => BinOpKind::CmpGe,
            mir::BinOp::Gt => BinOpKind::CmpGt,
            mir::BinOp::Offset => todo!(),
        }
    }
}
impl From<&mir::BinOp> for BinOpKind {
    fn from(value: &mir::BinOp) -> Self {
        BinOpKind::from(*value)
    }
}

pub enum ConstData {
    Bool(bool),
    Int(u128), // TODO: what about negative numbers? larger numbers?
}

pub enum TypeData<'vir> {
    Int,
    Bool,
    Domain(&'vir str), // TODO: identifiers
    DomainParams(&'vir str, &'vir [Type<'vir>]),
    // TODO: separate `TyParam` variant? `Domain` used for now
    Ref, // TODO: typed references ?
}

pub struct FieldData<'vir> {
    pub name: &'vir str, // TODO: identifiers
    pub ty: Type<'vir>,
}

pub struct DomainFunctionData<'vir> {
    pub unique: bool,
    pub name: &'vir str, // TODO: identifiers
    pub args: &'vir [Type<'vir>],
    pub ret: Type<'vir>,
}

pub enum CfgBlockLabelData {
    Start,
    End,
    BasicBlock(usize),
}

pub type AccFieldData<'vir> = crate::gendata::AccFieldGenData<'vir, !, !>;
pub type BinOpData<'vir> = crate::gendata::BinOpGenData<'vir, !, !>;
pub type CfgBlockData<'vir> = crate::gendata::CfgBlockGenData<'vir, !, !>;
pub type DomainAxiomData<'vir> = crate::gendata::DomainAxiomGenData<'vir, !, !>;
pub type DomainData<'vir> = crate::gendata::DomainGenData<'vir, !, !>;
pub type ExprData<'vir> = crate::gendata::ExprGenData<'vir, !, !>;
pub type ForallData<'vir> = crate::gendata::ForallGenData<'vir, !, !>;
pub type FuncAppData<'vir> = crate::gendata::FuncAppGenData<'vir, !, !>;
pub type FunctionData<'vir> = crate::gendata::FunctionGenData<'vir, !, !>;
pub type GotoIfData<'vir> = crate::gendata::GotoIfGenData<'vir, !, !>;
pub type LetData<'vir> = crate::gendata::LetGenData<'vir, !, !>;
pub type MethodCallData<'vir> = crate::gendata::MethodCallGenData<'vir, !, !>;
pub type MethodData<'vir> = crate::gendata::MethodGenData<'vir, !, !>;
pub type PredicateAppData<'vir> = crate::gendata::PredicateAppGenData<'vir, !, !>;
pub type PredicateData<'vir> = crate::gendata::PredicateGenData<'vir, !, !>;
pub type ProgramData<'vir> = crate::gendata::ProgramGenData<'vir, !, !>;
pub type PureAssignData<'vir> = crate::gendata::PureAssignGenData<'vir, !, !>;
pub type StmtData<'vir> = crate::gendata::StmtGenData<'vir, !, !>;
pub type TerminatorStmtData<'vir> = crate::gendata::TerminatorStmtGenData<'vir, !, !>;
pub type TernaryData<'vir> = crate::gendata::TernaryGenData<'vir, !, !>;
pub type UnOpData<'vir> = crate::gendata::UnOpGenData<'vir, !, !>;
pub type UnfoldingData<'vir> = crate::gendata::UnfoldingGenData<'vir, !, !>;
