// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::jar::viper::silver::ast::{self, Exp, Position, DomainFunc};
use super::{int_lit, int_lit_from_string};
use duchess::{IntoJava, JavaConstructor};
use duchess::java::lang::String as JavaString;

/// Unary floating-point operations
#[derive(Debug, Clone, Copy)]
pub enum UnOpFloat {
    Neg,
    Abs,
    IsZero,
    IsInfinite,
    IsNan,
    IsNegative,
    IsPositive,
    GetType,
    FromBV,
    ToBV,
}

/// Binary floating-point operations
#[derive(Debug, Clone, Copy)]
pub enum BinOpFloat {
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    Leq,
    Geq,
    Lt,
    Gt,
    Min,
    Max,
}

/// Floating-point size
#[derive(Debug)]
pub enum FloatSizeViper {
    F32,
    F64,
}

/// Unary bitwise operations on bitvectors
pub enum UnOpBv {
    Not,
    Neg,
    GetType,
    FromInt,
    ToInt,
    FromNat,
    ToNat,
}

/// Binary bitwise operations on bitvectors
pub enum BinOpBv {
    BitAnd,
    BitOr,
    BitXor,
    BvAdd,
    BvSub,
    BvMul,
    BvUDiv,
    BvShl,
    BvLShr,
    BvAShr,
}

/// Bitvector size
#[derive(Clone, Copy)]
pub enum BvSize {
    BV8,
    BV16,
    BV32,
    BV64,
    BV128,
}

impl BvSize {
    fn to_i32(self) -> i32 {
        match self {
            BvSize::BV8 => 8,
            BvSize::BV16 => 16,
            BvSize::BV32 => 32,
            BvSize::BV64 => 64,
            BvSize::BV128 => 128,
        }
    }
}

pub fn backend_bv8_lit(bits: u8) -> impl JavaConstructor<Exp> {
    let bv_factory = ast::utility::BVFactory::new(8);
    let from_int = bv_factory.from__int("bv8_from_int");
    backend_func_app(from_int, &[int_lit(bits as i64)], super::no_position())
}

pub fn backend_bv8_lit_str(bits: impl IntoJava<JavaString>) -> impl JavaConstructor<Exp> {
    let bv_factory = ast::utility::BVFactory::new(8);
    let from_int = bv_factory.from__int("bv8_from_int");
    backend_func_app(from_int, &[int_lit_from_string(bits)], super::no_position())
}

pub fn backend_bv16_lit(bits: u16) -> impl JavaConstructor<Exp> {
    let bv_factory = ast::utility::BVFactory::new(16);
    let from_int = bv_factory.from__int("bv16_from_int");
    backend_func_app(from_int, &[int_lit(bits as i64)], super::no_position())
}

pub fn backend_bv16_lit_str(bits: impl IntoJava<JavaString>) -> impl JavaConstructor<Exp> {
    let bv_factory = ast::utility::BVFactory::new(16);
    let from_int = bv_factory.from__int("bv16_from_int");
    backend_func_app(from_int, &[int_lit_from_string(bits)], super::no_position())
}

pub fn backend_bv32_lit(bits: u32) -> impl JavaConstructor<Exp> {
    let bv_factory = ast::utility::BVFactory::new(32);
    let from_int = bv_factory.from__int("bv32_from_int");
    backend_func_app(from_int, &[int_lit(bits as i64)], super::no_position())
}

pub fn backend_bv32_lit_str(bits: impl IntoJava<JavaString>) -> impl JavaConstructor<Exp> {
    let bv_factory = ast::utility::BVFactory::new(32);
    let from_int = bv_factory.from__int("bv32_from_int");
    backend_func_app(from_int, &[int_lit_from_string(bits)], super::no_position())
}

pub fn backend_bv64_lit(bits: u64) -> impl JavaConstructor<Exp> {
    let bv_factory = ast::utility::BVFactory::new(64);
    let from_int = bv_factory.from__int("bv64_from_int");
    backend_func_app(from_int, &[int_lit(bits as i64)], super::no_position())
}

pub fn backend_bv64_lit_str(bits: impl IntoJava<JavaString>) -> impl JavaConstructor<Exp> {
    let bv_factory = ast::utility::BVFactory::new(64);
    let from_int = bv_factory.from__int("bv64_to_int");
    backend_func_app(from_int, &[int_lit_from_string(bits)], super::no_position())
}

pub fn backend_bv128_lit(bits: u128) -> impl JavaConstructor<Exp> {
    let bv_factory = ast::utility::BVFactory::new(128);
    let from_int = bv_factory.from__int("bv128_from_int");
    backend_func_app(from_int, &[int_lit(bits as i64)], super::no_position())
}

pub fn backend_bv128_lit_str(bits: impl IntoJava<JavaString>) -> impl JavaConstructor<Exp> {
    let bv_factory = ast::utility::BVFactory::new(128);
    let from_int = bv_factory.from__int("bv128_from_int");
    backend_func_app(from_int, &[int_lit_from_string(bits)], super::no_position())
}

pub fn bv_factory(bv_size: BvSize) -> impl JavaConstructor<ast::utility::BVFactory> {
    ast::utility::BVFactory::new(bv_size.to_i32())
}

pub fn int_to_backend_bv(
    bv_size: BvSize, expr: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    let factory = bv_factory(bv_size);
    let from_int = factory.to__int(format!("bv{}_from_int", bv_size.to_i32()));
    backend_func_app(from_int, &[expr], super::no_position())
}

pub fn backend_bv_to_int(
    bv_size: BvSize, expr: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    let factory = bv_factory(bv_size);
    let to_int = factory.to__int(format!("bv{}_to_int", bv_size.to_i32()));
    backend_func_app(to_int, &[expr], super::no_position())
}

pub fn bv_binop(
    op_kind: BinOpBv, bv_size: BvSize, left: impl IntoJava<Exp>, right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    let factory = bv_factory(bv_size);
    let size = bv_size.to_i32();
    let op = match op_kind {
        BinOpBv::BitAnd => factory.and(format!("bv{size}_and")),
        BinOpBv::BitOr => factory.or(format!("bv{size}_or")),
        BinOpBv::BitXor => factory.xor(format!("bv{size}_xor")),
        BinOpBv::BvAdd => factory.add(format!("bv{size}_add")),
        BinOpBv::BvSub => factory.sub(format!("bv{size}_sub")),
        BinOpBv::BvMul => factory.mul(format!("bv{size}_mul")),
        BinOpBv::BvUDiv => factory.udiv(format!("bv{size}_udiv")),
        BinOpBv::BvShl => factory.shl(format!("bv{size}_shl")),
        BinOpBv::BvLShr => factory.lshr(format!("bv{size}_lshr")),
        BinOpBv::BvAShr => factory.ashr(format!("bv{size}_ashr")),
    };
    backend_func_app(op, &[left, right], super::no_position())
}

pub fn bv_unnop(
    op_kind: UnOpBv, bv_size: BvSize, arg: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    let factory = bv_factory(bv_size);
    let op = match op_kind {
        UnOpBv::Not => factory.not("not"),
        UnOpBv::Neg => factory.neg("neg"),
        x => unimplemented!("unimplemented unop {x:?} for bitvectors"),
    };
    backend_func_app(op, &[arg], super::no_position())
}

pub fn float_binop(
    op_kind: BinOpFloat,
    f_size: FloatSizeViper,
    left: impl IntoJava<Exp>,
    right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    let rm = ast::utility::RoundingMode::RNE();
    let factory = match f_size {
        FloatSizeViper::F32 => ast::utility::FloatFactory::new(24, 8, rm),
        FloatSizeViper::F64 => ast::utility::FloatFactory::new(52, 12, rm),
    };
    let size = match f_size {
        FloatSizeViper::F32 => 32,
        FloatSizeViper::F64 => 64,
    };
    let op = match op_kind {
        // create FloatFactory function to call
        BinOpFloat::Add => factory.add(format!("f{size}_fp_add")),
        BinOpFloat::Sub => factory.sub(format!("f{size}_fp_sub")),
        BinOpFloat::Mul => factory.mul(format!("f{size}_fp_mul")),
        BinOpFloat::Div => factory.div(format!("f{size}_fp_div")),
        BinOpFloat::Min => factory.min(format!("f{size}_fp_min")),
        BinOpFloat::Max => factory.max(format!("f{size}_fp_max")),
        BinOpFloat::Eq => factory.eq(format!("f{size}_fp_eq")),
        BinOpFloat::Leq => factory.leq(format!("f{size}_fp_leq")),
        BinOpFloat::Geq => factory.geq(format!("f{size}_fp_geq")),
        BinOpFloat::Lt => factory.lt(format!("f{size}_fp_lt")),
        BinOpFloat::Gt => factory.gt(format!("f{size}_fp_gt")),
    };
    backend_func_app(op, &[left, right], super::no_position())
}

pub fn float_unop(
    op_kind: UnOpFloat, f_size: FloatSizeViper, arg: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    let rm = ast::utility::RoundingMode::RNE();
    let factory = match f_size {
        FloatSizeViper::F32 => ast::utility::FloatFactory::new(24, 8, rm),
        FloatSizeViper::F64 => ast::utility::FloatFactory::new(52, 12, rm),
    };
    let size = match f_size {
        FloatSizeViper::F32 => 32,
        FloatSizeViper::F64 => 64,
    };
    let op = match op_kind {
        UnOpFloat::Neg => factory.neg(format!("f{size}_fp_neg")),
        UnOpFloat::Abs => factory.abs(format!("f{size}_fp_abs")),
        UnOpFloat::IsZero => factory.isZero(format!("f{size}_fp_is_zero")),
        UnOpFloat::IsInfinite => factory.isInfinite(format!("f{size}_fp_is_infinite")),
        UnOpFloat::IsNan => factory.isNaN(format!("f{size}_fp_is_nan")),
        UnOpFloat::IsNegative => factory.isNegative(format!("f{size}_fp_is_negative")),
        UnOpFloat::IsPositive => factory.isPositive(format!("f{size}_fp_is_positive")),
        UnOpFloat::GetType => unimplemented!(),
        UnOpFloat::FromBV => unimplemented!(),
        UnOpFloat::ToBV => unimplemented!(),
    };

    backend_func_app(op, &[arg], super::no_position())
}

pub fn backend_f32_lit(bits: u32) -> impl JavaConstructor<Exp> {
    let bv = backend_bv32_lit(bits);
    let rm = ast::utility::RoundingMode::RNE();
    let float_factory = ast::utility::FloatFactory::new(24, 8, rm);
    let from_bv = float_factory.from__bv("f32_from_bv");
    backend_func_app(from_bv, &[bv], super::no_position())
}

pub fn backend_f64_lit(bits: u64) -> impl JavaConstructor<Exp> {
    let bv = backend_bv64_lit(bits);
    let rm = ast::utility::RoundingMode::RNE();
    let float_factory = ast::utility::FloatFactory::new(52, 12, rm);
    let from_bv = float_factory.from__bv("f64_from_bv");
    backend_func_app(from_bv, &[bv], super::no_position())
}

pub fn backend_func_app(
    backend_function: impl IntoJava<DomainFunc>,
    args: &[impl IntoJava<Exp>],
    pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    ast::BackendFuncApp__::get_module()
        .apply(backend_function, args)
        .apply(
            pos,
            super::no_info(),
            super::no_trafos(),
        )
}
