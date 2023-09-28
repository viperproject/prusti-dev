use std::fmt::Debug;

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

#[derive(Clone, Copy, Debug)]
pub enum BinOpKind {
    CmpEq,
    CmpGt,
    CmpLt,
    And,
    Add,
    // ...
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
