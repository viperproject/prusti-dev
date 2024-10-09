use std::collections::HashMap;
use std::fmt::Debug;
use serde::{Serialize, Deserialize};

use prusti_rustc_interface::middle::mir;

use crate::{debug_info::DebugInfo, refs::*, viper_ident::ViperIdent, CallableIdent, FunctionIdent, UnknownArity};

#[derive(Serialize, Deserialize, Hash)]
pub struct LocalData<'vir> {
    #[serde(with = "crate::serde::serde_str")] pub name: &'vir str, // TODO: identifiers
    #[serde(with = "crate::serde::serde_ref")] pub ty: Type<'vir>,
    pub debug_info: DebugInfo<'vir>
}

#[derive(Eq, PartialEq)]
#[derive(Serialize, Deserialize, Hash)]
pub struct LocalDeclData<'vir> {
    #[serde(with = "crate::serde::serde_str")] pub name: &'vir str, // TODO: identifiers
    #[serde(with = "crate::serde::serde_ref")] pub ty: Type<'vir>,
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Serialize, Deserialize, Hash)]
pub enum UnOpKind {
    Neg,
    Not,
}
impl From<mir::UnOp> for UnOpKind {
    fn from(value: mir::UnOp) -> Self {
        match value {
            mir::UnOp::Not => UnOpKind::Not,
            mir::UnOp::Neg => UnOpKind::Neg,
            mir::UnOp::PtrMetadata => todo!(),
        }
    }
}
impl From<&mir::UnOp> for UnOpKind {
    fn from(value: &mir::UnOp) -> Self {
        UnOpKind::from(*value)
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Serialize, Deserialize, Hash)]
pub enum BinOpKind {
    CmpEq,
    CmpNe,
    CmpGt,
    CmpLt,
    CmpGe,
    CmpLe,
    And,
    Or,
    Implies,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    // ...
}
impl From<mir::BinOp> for BinOpKind {
    fn from(value: mir::BinOp) -> Self {
        match value {
            mir::BinOp::Add => BinOpKind::Add,
            mir::BinOp::AddUnchecked => todo!(),
            mir::BinOp::Sub => BinOpKind::Sub,
            mir::BinOp::SubUnchecked => todo!(),
            mir::BinOp::Mul => BinOpKind::Mul,
            mir::BinOp::MulUnchecked => todo!(),
            mir::BinOp::Div => BinOpKind::Div,
            mir::BinOp::Rem => BinOpKind::Mod,
            mir::BinOp::BitXor => todo!(),
            // TODO: this is a temporary workaround,
            // we need to fix this for integers and
            // do non-short-circuiting for booleans.
            mir::BinOp::BitAnd => BinOpKind::And,
            mir::BinOp::BitOr => BinOpKind::Or,
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
            mir::BinOp::AddWithOverflow => todo!(),
            mir::BinOp::SubWithOverflow => todo!(),
            mir::BinOp::MulWithOverflow => todo!(),
            mir::BinOp::Cmp => todo!(),
        }
    }
}
impl From<&mir::BinOp> for BinOpKind {
    fn from(value: &mir::BinOp) -> Self {
        BinOpKind::from(*value)
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Serialize, Deserialize, Hash)]
pub enum ConstData {
    Bool(bool),
    Int(u128), // TODO: what about negative numbers? larger numbers?
    Wildcard,
    Null,
}

impl ConstData {
    pub fn ty(&self) -> Type<'static> {
        match self {
            ConstData::Bool(_) => &TypeData::Bool,
            ConstData::Int(_) => &TypeData::Int,
            ConstData::Wildcard => &TypeData::Perm,
            ConstData::Null => &TypeData::Ref
        }
    }
}

#[derive(PartialEq, Eq, Ord, PartialOrd, Serialize, Deserialize, Hash)]
pub enum TypeData<'vir> {
    Int,
    Bool,
    DomainTypeParam(DomainParamData<'vir>), // TODO: identifiers
    Domain(
        #[serde(with = "crate::serde::serde_str")] &'vir str, // TODO: identifiers
        #[serde(with = "crate::serde::serde_slice")] &'vir [Type<'vir>]
    ),
    // TODO: separate `TyParam` variant? `Domain` used for now
    Ref, // TODO: typed references ?
    Perm,
    Predicate, // The type of a predicate application
    Unsupported(UnsupportedType<'vir>)
}

#[derive(PartialEq, Eq, Clone, Ord, PartialOrd, Serialize, Deserialize, Hash)]
pub struct UnsupportedType<'vir> {
    #[serde(with = "crate::serde::serde_str")] pub name: &'vir str,
}

pub type TySubsts<'vir> = HashMap<&'vir str, Type<'vir>>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Ord, PartialOrd, Serialize, Deserialize, Hash)]
pub struct DomainParamData<'vir> {
    #[serde(with = "crate::serde::serde_str")] pub name: &'vir str, // TODO: identifiers
}

#[derive(PartialEq, Eq, Clone, Serialize, Deserialize, Hash)]
pub struct FieldData<'vir> {
    #[serde(with = "crate::serde::serde_str")] pub name: &'vir str, // TODO: identifiers
    #[serde(with = "crate::serde::serde_ref")] pub ty: Type<'vir>,
}

#[derive(PartialEq, Eq, Clone, Serialize, Deserialize, Hash)]
#[serde(bound(deserialize = "'de: 'vir"))]
pub struct DomainFunctionData<'vir> {
    pub unique: bool,
    pub name: ViperIdent<'vir>,
    #[serde(with = "crate::serde::serde_slice")] pub args: &'vir [Type<'vir>],
    #[serde(with = "crate::serde::serde_ref")] pub ret: Type<'vir>,
}

impl <'vir> DomainFunctionData<'vir> {
    pub fn ident(&self) -> FunctionIdent<'vir, UnknownArity<'vir>> {
        FunctionIdent::new(
            self.name,
            UnknownArity::new(self.args),
            self.ret,
        )
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Serialize, Deserialize, Hash)]
pub enum CfgBlockLabelData {
    Start,
    End,
    BasicBlock(usize),
}

impl CfgBlockLabelData {
    pub fn name(&self) -> String {
        match self {
            Self::Start => "start".to_string(),
            Self::End => "end".to_string(),
            Self::BasicBlock(idx) => format!("bb_{idx}"),
        }
    }
}

pub type AccFieldData<'vir> = crate::gendata::AccFieldGenData<'vir, !, !>;
pub type BinOpData<'vir> = crate::gendata::BinOpGenData<'vir, !, !>;
pub type CfgBlockData<'vir> = crate::gendata::CfgBlockGenData<'vir, !, !>;
pub type DomainAxiomData<'vir> = crate::gendata::DomainAxiomGenData<'vir, !, !>;
pub type DomainData<'vir> = crate::gendata::DomainGenData<'vir, !, !>;
pub type ExprData<'vir> = crate::gendata::ExprGenData<'vir, !, !>;
pub type ExprKindData<'vir> = crate::gendata::ExprKindGenData<'vir, ! ,!>;
pub type ForallData<'vir> = crate::gendata::ForallGenData<'vir, !, !>;
pub type FuncAppData<'vir> = crate::gendata::FuncAppGenData<'vir, !, !>;
pub type FunctionData<'vir> = crate::gendata::FunctionGenData<'vir, !, !>;
pub type GotoIfData<'vir> = crate::gendata::GotoIfGenData<'vir, !, !>;
pub type LetData<'vir> = crate::gendata::LetGenData<'vir, !, !>;
pub type MethodData<'vir> = crate::gendata::MethodGenData<'vir, !, !>;
pub type MethodBodyData<'vir> = crate::gendata::MethodBodyGenData<'vir, !, !>;
pub type MethodCallData<'vir> = crate::gendata::MethodCallGenData<'vir, !, !>;
pub type PredicateAppData<'vir> = crate::gendata::PredicateAppGenData<'vir, !, !>;
pub type PredicateData<'vir> = crate::gendata::PredicateGenData<'vir, !, !>;
pub type ProgramData<'vir> = crate::gendata::ProgramGenData<'vir, !, !>;
pub type PureAssignData<'vir> = crate::gendata::PureAssignGenData<'vir, !, !>;
pub type StmtData<'vir> = crate::gendata::StmtGenData<'vir, !, !>;
pub type StmtKindData<'vir> = crate::gendata::StmtKindGenData<'vir, !, !>;
pub type TerminatorStmtData<'vir> = crate::gendata::TerminatorStmtGenData<'vir, !, !>;
pub type TernaryData<'vir> = crate::gendata::TernaryGenData<'vir, !, !>;
pub type TriggerData<'vir> = crate::gendata::TriggerGenData<'vir, !, !>;
pub type UnOpData<'vir> = crate::gendata::UnOpGenData<'vir, !, !>;
pub type UnfoldingData<'vir> = crate::gendata::UnfoldingGenData<'vir, !, !>;
