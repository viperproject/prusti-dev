// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::ast_factory::{
    structs::{DomainFunc, Expr, Field, LocalVarDecl, Location, Position, Trigger, Type},
    AstFactory,
};
use jni::objects::JObject;
use viper_sys::wrappers::viper::silver::ast;

// Floating-Point Operations
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

// Floating-Point Size
#[derive(Debug)]
pub enum FloatSizeViper {
    F32,
    F64,
}

// Bitwise Operations on Backend Bitvectors
pub enum UnOpBv {
    Not,
    Neg,
    GetType,
    FromInt,
    ToInt,
    FromNat,
    ToNat,
}

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

impl<'a> AstFactory<'a> {
    pub fn add_with_pos(&self, left: Expr, right: Expr, pos: Position) -> Expr<'a> {
        build_ast_node_with_pos!(
            self,
            Expr,
            ast::Add,
            left.to_jobject(),
            right.to_jobject(),
            pos.to_jobject()
        )
    }
    pub fn add(&self, left: Expr, right: Expr) -> Expr<'a> {
        self.add_with_pos(left, right, self.no_position())
    }

    pub fn sub_with_pos(&self, left: Expr, right: Expr, pos: Position) -> Expr<'a> {
        build_ast_node_with_pos!(
            self,
            Expr,
            ast::Sub,
            left.to_jobject(),
            right.to_jobject(),
            pos.to_jobject()
        )
    }

    pub fn sub(&self, left: Expr, right: Expr) -> Expr<'a> {
        self.sub_with_pos(left, right, self.no_position())
    }

    pub fn mul_with_pos(&self, left: Expr, right: Expr, pos: Position) -> Expr<'a> {
        build_ast_node_with_pos!(
            self,
            Expr,
            ast::Mul,
            left.to_jobject(),
            right.to_jobject(),
            pos.to_jobject()
        )
    }

    pub fn mul(&self, left: Expr, right: Expr) -> Expr<'a> {
        self.mul_with_pos(left, right, self.no_position())
    }

    pub fn div_with_pos(&self, left: Expr, right: Expr, pos: Position) -> Expr<'a> {
        build_ast_node_with_pos!(
            self,
            Expr,
            ast::Div,
            left.to_jobject(),
            right.to_jobject(),
            pos.to_jobject()
        )
    }

    pub fn div(&self, left: Expr, right: Expr) -> Expr<'a> {
        self.div_with_pos(left, right, self.no_position())
    }

    pub fn module_with_pos(&self, left: Expr, right: Expr, pos: Position) -> Expr<'a> {
        build_ast_node_with_pos!(
            self,
            Expr,
            ast::Mod,
            left.to_jobject(),
            right.to_jobject(),
            pos.to_jobject()
        )
    }

    pub fn module(&self, left: Expr, right: Expr) -> Expr<'a> {
        self.module_with_pos(left, right, self.no_position())
    }

    pub fn lt_cmp_with_pos(&self, left: Expr, right: Expr, pos: Position) -> Expr<'a> {
        build_ast_node_with_pos!(
            self,
            Expr,
            ast::LtCmp,
            left.to_jobject(),
            right.to_jobject(),
            pos.to_jobject()
        )
    }

    pub fn lt_cmp(&self, left: Expr, right: Expr) -> Expr<'a> {
        self.lt_cmp_with_pos(left, right, self.no_position())
    }

    pub fn le_cmp_with_pos(&self, left: Expr, right: Expr, pos: Position) -> Expr<'a> {
        build_ast_node_with_pos!(
            self,
            Expr,
            ast::LeCmp,
            left.to_jobject(),
            right.to_jobject(),
            pos.to_jobject()
        )
    }

    pub fn le_cmp(&self, left: Expr, right: Expr) -> Expr<'a> {
        self.le_cmp_with_pos(left, right, self.no_position())
    }

    pub fn gt_cmp_with_pos(&self, left: Expr, right: Expr, pos: Position) -> Expr<'a> {
        build_ast_node_with_pos!(
            self,
            Expr,
            ast::GtCmp,
            left.to_jobject(),
            right.to_jobject(),
            pos.to_jobject()
        )
    }

    pub fn gt_cmp(&self, left: Expr, right: Expr) -> Expr<'a> {
        self.gt_cmp_with_pos(left, right, self.no_position())
    }

    pub fn ge_cmp_with_pos(&self, left: Expr, right: Expr, pos: Position) -> Expr<'a> {
        build_ast_node_with_pos!(
            self,
            Expr,
            ast::GeCmp,
            left.to_jobject(),
            right.to_jobject(),
            pos.to_jobject()
        )
    }

    pub fn ge_cmp(&self, left: Expr, right: Expr) -> Expr<'a> {
        self.ge_cmp_with_pos(left, right, self.no_position())
    }

    pub fn eq_cmp_with_pos(&self, left: Expr, right: Expr, pos: Position) -> Expr<'a> {
        build_ast_node_with_pos!(
            self,
            Expr,
            ast::EqCmp,
            left.to_jobject(),
            right.to_jobject(),
            pos.to_jobject()
        )
    }

    pub fn eq_cmp(&self, left: Expr, right: Expr) -> Expr<'a> {
        self.eq_cmp_with_pos(left, right, self.no_position())
    }

    pub fn ne_cmp_with_pos(&self, left: Expr, right: Expr, pos: Position) -> Expr<'a> {
        build_ast_node_with_pos!(
            self,
            Expr,
            ast::NeCmp,
            left.to_jobject(),
            right.to_jobject(),
            pos.to_jobject()
        )
    }

    pub fn ne_cmp(&self, left: Expr, right: Expr) -> Expr<'a> {
        self.ne_cmp_with_pos(left, right, self.no_position())
    }

    pub fn int_lit_with_pos(&self, i: i64, pos: Position) -> Expr<'a> {
        let big_i = self.jni.new_big_int(&i);
        build_ast_node_with_pos!(self, Expr, ast::IntLit, big_i, pos.to_jobject())
    }

    pub fn int_lit(&self, i: i64) -> Expr<'a> {
        self.int_lit_with_pos(i, self.no_position())
    }

    pub fn int_lit_from_ref_with_pos(&self, i: &dyn ToString, pos: Position) -> Expr<'a> {
        let big_i = self.jni.new_big_int(i);
        build_ast_node_with_pos!(self, Expr, ast::IntLit, big_i, pos.to_jobject())
    }

    pub fn int_lit_from_ref(&self, i: &dyn ToString) -> Expr<'a> {
        self.int_lit_from_ref_with_pos(i, self.no_position())
    }

    pub fn minus_with_pos(&self, expr: Expr, pos: Position) -> Expr<'a> {
        build_ast_node_with_pos!(self, Expr, ast::Minus, expr.to_jobject(), pos.to_jobject())
    }

    pub fn minus(&self, expr: Expr) -> Expr<'a> {
        self.minus_with_pos(expr, self.no_position())
    }

    // Backend Bitvectors
    pub fn backend_bv8_lit(&self, bits: u8) -> Expr<'a> {
        let bv_factory_ = ast::utility::BVFactory::with(self.env);
        let bv_factory = ast::utility::BVFactory::new(&bv_factory_, 8).unwrap();
        let from_int = ast::utility::BVFactory::call_from__int(
            &bv_factory_,
            bv_factory,
            self.jni.new_string("bv8_from_int"),
        )
        .unwrap();
        self.backend_func_app(from_int, &[self.int_lit(bits as i64)], self.no_position())
    }

    pub fn backend_bv8_lit_str(&self, bits: &dyn ToString) -> Expr<'a> {
        let bv_factory_ = ast::utility::BVFactory::with(self.env);
        let bv_factory = ast::utility::BVFactory::new(&bv_factory_, 8).unwrap();
        let from_int = ast::utility::BVFactory::call_from__int(
            &bv_factory_,
            bv_factory,
            self.jni.new_string("bv8_from_int"),
        )
        .unwrap();
        self.backend_func_app(from_int, &[self.int_lit_from_ref(bits)], self.no_position())
    }

    pub fn backend_bv16_lit(&self, bits: u16) -> Expr<'a> {
        let bv_factory_ = ast::utility::BVFactory::with(self.env);
        let bv_factory = ast::utility::BVFactory::new(&bv_factory_, 16).unwrap();
        let from_int = ast::utility::BVFactory::call_from__int(
            &bv_factory_,
            bv_factory,
            self.jni.new_string("bv16_from_int"),
        )
        .unwrap();
        self.backend_func_app(from_int, &[self.int_lit(bits as i64)], self.no_position())
    }

    pub fn backend_bv16_lit_str(&self, bits: &dyn ToString) -> Expr<'a> {
        let bv_factory_ = ast::utility::BVFactory::with(self.env);
        let bv_factory = ast::utility::BVFactory::new(&bv_factory_, 16).unwrap();
        let from_int = ast::utility::BVFactory::call_from__int(
            &bv_factory_,
            bv_factory,
            self.jni.new_string("bv16_from_int"),
        )
        .unwrap();
        self.backend_func_app(from_int, &[self.int_lit_from_ref(bits)], self.no_position())
    }

    pub fn backend_bv32_lit(&self, bits: u32) -> Expr<'a> {
        let bv_factory_ = ast::utility::BVFactory::with(self.env);
        let bv_factory = ast::utility::BVFactory::new(&bv_factory_, 32).unwrap();
        let from_int = ast::utility::BVFactory::call_from__int(
            &bv_factory_,
            bv_factory,
            self.jni.new_string("bv32_from_int"),
        )
        .unwrap();
        self.backend_func_app(from_int, &[self.int_lit(bits as i64)], self.no_position())
    }

    pub fn backend_bv32_lit_str(&self, bits: &dyn ToString) -> Expr<'a> {
        let bv_factory_ = ast::utility::BVFactory::with(self.env);
        let bv_factory = ast::utility::BVFactory::new(&bv_factory_, 32).unwrap();
        let from_int = ast::utility::BVFactory::call_from__int(
            &bv_factory_,
            bv_factory,
            self.jni.new_string("bv32_from_int"),
        )
        .unwrap();
        self.backend_func_app(from_int, &[self.int_lit_from_ref(bits)], self.no_position())
    }

    pub fn backend_bv64_lit(&self, bits: u64) -> Expr<'a> {
        let bv_factory_ = ast::utility::BVFactory::with(self.env);
        let bv_factory = ast::utility::BVFactory::new(&bv_factory_, 64).unwrap();
        let from_int = ast::utility::BVFactory::call_from__int(
            &bv_factory_,
            bv_factory,
            self.jni.new_string("bv64_from_int"),
        )
        .unwrap();
        self.backend_func_app(from_int, &[self.int_lit(bits as i64)], self.no_position())
    }

    pub fn backend_bv64_lit_str(&self, bits: &dyn ToString) -> Expr<'a> {
        let bv_factory_ = ast::utility::BVFactory::with(self.env);
        let bv_factory = ast::utility::BVFactory::new(&bv_factory_, 64).unwrap();
        let from_int = ast::utility::BVFactory::call_from__int(
            &bv_factory_,
            bv_factory,
            self.jni.new_string("bv64_to_int"),
        )
        .unwrap();
        self.backend_func_app(from_int, &[self.int_lit_from_ref(bits)], self.no_position())
    }

    pub fn backend_bv128_lit(&self, bits: u128) -> Expr<'a> {
        let bv_factory_ = ast::utility::BVFactory::with(self.env);
        let bv_factory = ast::utility::BVFactory::new(&bv_factory_, 128).unwrap();
        let from_int = ast::utility::BVFactory::call_from__int(
            &bv_factory_,
            bv_factory,
            self.jni.new_string("bv128_from_int"),
        )
        .unwrap();
        self.backend_func_app(from_int, &[self.int_lit(bits as i64)], self.no_position())
    }

    pub fn backend_bv128_lit_str(&self, bits: &dyn ToString) -> Expr<'a> {
        let bv_factory_ = ast::utility::BVFactory::with(self.env);
        let bv_factory = ast::utility::BVFactory::new(&bv_factory_, 128).unwrap();
        let from_int = ast::utility::BVFactory::call_from__int(
            &bv_factory_,
            bv_factory,
            self.jni.new_string("bv128_from_int"),
        )
        .unwrap();
        self.backend_func_app(from_int, &[self.int_lit_from_ref(bits)], self.no_position())
    }

    pub fn bv_factory(&self, bv_size: BvSize) -> (ast::utility::BVFactory<'a>, JObject<'a>) {
        let factory_ = ast::utility::BVFactory::with(self.env); // FloatFactory
        let factory = ast::utility::BVFactory::new(&factory_, bv_size.to_i32()).unwrap();
        (factory_, factory)
    }

    pub fn int_to_backend_bv(&self, bv_size: BvSize, expr: Expr<'a>) -> Expr<'a> {
        let (factory_, factory) = self.bv_factory(bv_size);
        let from_int = ast::utility::BVFactory::call_to__int(
            &factory_,
            factory,
            self.jni
                .new_string(format!("bv{}_from_int", bv_size.to_i32())),
        )
        .unwrap();
        self.backend_func_app(from_int, &[expr], self.no_position())
    }

    pub fn backend_bv_to_int(&self, bv_size: BvSize, expr: Expr<'a>) -> Expr<'a> {
        let (factory_, factory) = self.bv_factory(bv_size);
        let to_int = ast::utility::BVFactory::call_to__int(
            &factory_,
            factory,
            self.jni
                .new_string(format!("bv{}_to_int", bv_size.to_i32())),
        )
        .unwrap();
        self.backend_func_app(to_int, &[expr], self.no_position())
    }

    pub fn bv_binop(&self, op_kind: BinOpBv, bv_size: BvSize, left: Expr, right: Expr) -> Expr<'a> {
        let (factory_, factory) = self.bv_factory(bv_size);
        let size = bv_size.to_i32();
        let op = match op_kind {
            BinOpBv::BitAnd => ast::utility::BVFactory::call_and(
                &factory_,
                factory,
                self.jni.new_string(&format!("bv{size}_and")),
            ),
            BinOpBv::BitOr => ast::utility::BVFactory::call_or(
                &factory_,
                factory,
                self.jni.new_string(&format!("bv{size}_or")),
            ),
            BinOpBv::BitXor => ast::utility::BVFactory::call_xor(
                &factory_,
                factory,
                self.jni.new_string(&format!("bv{size}_xor")),
            ),
            BinOpBv::BvAdd => ast::utility::BVFactory::call_add(
                &factory_,
                factory,
                self.jni.new_string(&format!("bv{size}_add")),
            ),
            BinOpBv::BvSub => ast::utility::BVFactory::call_sub(
                &factory_,
                factory,
                self.jni.new_string(&format!("bv{size}_sub")),
            ),
            BinOpBv::BvMul => ast::utility::BVFactory::call_mul(
                &factory_,
                factory,
                self.jni.new_string(&format!("bv{size}_mul")),
            ),
            BinOpBv::BvUDiv => ast::utility::BVFactory::call_udiv(
                &factory_,
                factory,
                self.jni.new_string(&format!("bv{size}_udiv")),
            ),
            BinOpBv::BvShl => ast::utility::BVFactory::call_shl(
                &factory_,
                factory,
                self.jni.new_string(&format!("bv{size}_shl")),
            ),
            BinOpBv::BvLShr => ast::utility::BVFactory::call_lshr(
                &factory_,
                factory,
                self.jni.new_string(&format!("bv{size}_lshr")),
            ),
            BinOpBv::BvAShr => ast::utility::BVFactory::call_ashr(
                &factory_,
                factory,
                self.jni.new_string(&format!("bv{size}_ashr")),
            ),
        }
        .unwrap();
        self.backend_func_app(op, &[left, right], self.no_position())
    }

    pub fn bv_unnop(&self, op_kind: UnOpBv, bv_size: BvSize, arg: Expr) -> Expr<'a> {
        let (factory_, factory) = self.bv_factory(bv_size);
        let op = match op_kind {
            UnOpBv::Not => {
                ast::utility::BVFactory::call_not(&factory_, factory, self.jni.new_string("not"))
            }
            UnOpBv::Neg => {
                ast::utility::BVFactory::call_neg(&factory_, factory, self.jni.new_string("neg"))
            }
            _ => unreachable!("unimplemented unop for bitvectors"),
        }
        .unwrap();
        self.backend_func_app(op, &[arg], self.no_position())
    }

    // Backend Floating-Points
    pub fn float_binop(
        &self,
        op_kind: BinOpFloat,
        f_size: FloatSizeViper,
        left: Expr,
        right: Expr,
    ) -> Expr<'a> {
        let rm = ast::utility::RoundingMode::with(self.env)
            .call_RNE()
            .unwrap(); // Rounding mode
        let factory_ = ast::utility::FloatFactory::with(self.env); // FloatFactory
        let factory = match f_size {
            //
            FloatSizeViper::F32 => ast::utility::FloatFactory::new(&factory_, 24, 8, rm),
            FloatSizeViper::F64 => ast::utility::FloatFactory::new(&factory_, 52, 12, rm),
        }
        .unwrap();
        let size = match f_size {
            FloatSizeViper::F32 => 32,
            FloatSizeViper::F64 => 64,
        };
        let op = match op_kind {
            // create FloatFactory function to call
            BinOpFloat::Add => ast::utility::FloatFactory::call_add(
                &factory_,
                factory,
                self.jni.new_string(format!("f{size}_fp_add")),
            ),
            BinOpFloat::Sub => ast::utility::FloatFactory::call_sub(
                &factory_,
                factory,
                self.jni.new_string(format!("f{size}_fp_sub")),
            ),
            BinOpFloat::Mul => ast::utility::FloatFactory::call_mul(
                &factory_,
                factory,
                self.jni.new_string(format!("f{size}_fp_mul")),
            ),
            BinOpFloat::Div => ast::utility::FloatFactory::call_div(
                &factory_,
                factory,
                self.jni.new_string(format!("f{size}_fp_div")),
            ),
            BinOpFloat::Min => ast::utility::FloatFactory::call_min(
                &factory_,
                factory,
                self.jni.new_string(format!("f{size}_fp_min")),
            ),
            BinOpFloat::Max => ast::utility::FloatFactory::call_max(
                &factory_,
                factory,
                self.jni.new_string(format!("f{size}_fp_max")),
            ),
            BinOpFloat::Eq => ast::utility::FloatFactory::call_eq(
                &factory_,
                factory,
                self.jni.new_string(format!("f{size}_fp_eq")),
            ),
            BinOpFloat::Leq => ast::utility::FloatFactory::call_leq(
                &factory_,
                factory,
                self.jni.new_string(format!("f{size}_fp_leq")),
            ),
            BinOpFloat::Geq => ast::utility::FloatFactory::call_geq(
                &factory_,
                factory,
                self.jni.new_string(format!("f{size}_fp_geq")),
            ),
            BinOpFloat::Lt => ast::utility::FloatFactory::call_lt(
                &factory_,
                factory,
                self.jni.new_string(format!("f{size}_fp_lt")),
            ),
            BinOpFloat::Gt => ast::utility::FloatFactory::call_gt(
                &factory_,
                factory,
                self.jni.new_string(format!("f{size}_fp_gt")),
            ),
        }
        .unwrap();
        self.backend_func_app(op, &[left, right], self.no_position())
    }

    pub fn float_unop(&self, op_kind: UnOpFloat, f_size: FloatSizeViper, arg: Expr) -> Expr<'a> {
        let rm = ast::utility::RoundingMode::with(self.env)
            .call_RNE()
            .unwrap(); // Rounding mode
        let factory_ = ast::utility::FloatFactory::with(self.env); // FloatFactory
        let factory = match f_size {
            // FloatFactory JObject
            FloatSizeViper::F32 => ast::utility::FloatFactory::new(&factory_, 24, 8, rm),
            FloatSizeViper::F64 => ast::utility::FloatFactory::new(&factory_, 52, 12, rm),
        }
        .unwrap();
        let size = match f_size {
            FloatSizeViper::F32 => 32,
            FloatSizeViper::F64 => 64,
        };
        let op = match op_kind {
            UnOpFloat::Neg => ast::utility::FloatFactory::call_neg(
                &factory_,
                factory,
                self.jni.new_string(format!("f{size}_fp_neg")),
            ),
            UnOpFloat::Abs => ast::utility::FloatFactory::call_abs(
                &factory_,
                factory,
                self.jni.new_string(format!("f{size}_fp_abs")),
            ),
            UnOpFloat::IsZero => ast::utility::FloatFactory::call_isZero(
                &factory_,
                factory,
                self.jni.new_string(format!("f{size}_fp_is_zero")),
            ),
            UnOpFloat::IsInfinite => ast::utility::FloatFactory::call_isInfinite(
                &factory_,
                factory,
                self.jni.new_string(format!("f{size}_fp_is_infinite")),
            ),
            UnOpFloat::IsNan => ast::utility::FloatFactory::call_isNaN(
                &factory_,
                factory,
                self.jni.new_string(format!("f{size}_fp_is_nan")),
            ),
            UnOpFloat::IsNegative => ast::utility::FloatFactory::call_isNegative(
                &factory_,
                factory,
                self.jni.new_string(format!("f{size}_fp_is_negative")),
            ),
            UnOpFloat::IsPositive => ast::utility::FloatFactory::call_isPositive(
                &factory_,
                factory,
                self.jni.new_string(format!("f{size}_fp_is_positive")),
            ),
            UnOpFloat::GetType => todo!(),
            UnOpFloat::FromBV => todo!(),
            UnOpFloat::ToBV => todo!(),
        }
        .unwrap();

        self.backend_func_app(op, &[arg], self.no_position())
    }

    pub fn backend_f32_lit(&self, bits: u32) -> Expr<'a> {
        let bv = self.backend_bv32_lit(bits);
        let rm = ast::utility::RoundingMode::with(self.env)
            .call_RNE()
            .unwrap(); // Rounding mode
        let float_factory_ = ast::utility::FloatFactory::with(self.env); // FloatFactory
        let float_factory = ast::utility::FloatFactory::new(&float_factory_, 24, 8, rm).unwrap(); // FloatFactory JObject
        let from_bv = ast::utility::FloatFactory::call_from__bv(
            &float_factory_,
            float_factory,
            self.jni.new_string("f32_from_bv"),
        )
        .unwrap();
        self.backend_func_app(from_bv, &[bv], self.no_position())
    }

    pub fn backend_f64_lit(&self, bits: u64) -> Expr<'a> {
        let bv = self.backend_bv64_lit(bits);
        let rm = ast::utility::RoundingMode::with(self.env)
            .call_RNE()
            .unwrap(); // Rounding mode
        let float_factory_ = ast::utility::FloatFactory::with(self.env); // FloatFactory
        let float_factory = ast::utility::FloatFactory::new(&float_factory_, 52, 12, rm).unwrap(); // FloatFactory JObject
        let from_bv = ast::utility::FloatFactory::call_from__bv(
            &float_factory_,
            float_factory,
            self.jni.new_string("f64_from_bv"),
        )
        .unwrap();
        self.backend_func_app(from_bv, &[bv], self.no_position())
    }

    pub fn or_with_pos(&self, left: Expr, right: Expr, pos: Position) -> Expr<'a> {
        build_ast_node_with_pos!(
            self,
            Expr,
            ast::Or,
            left.to_jobject(),
            right.to_jobject(),
            pos.to_jobject()
        )
    }

    pub fn or(&self, left: Expr, right: Expr) -> Expr<'a> {
        self.or_with_pos(left, right, self.no_position())
    }

    pub fn and_with_pos(&self, left: Expr, right: Expr, pos: Position) -> Expr<'a> {
        build_ast_node_with_pos!(
            self,
            Expr,
            ast::And,
            left.to_jobject(),
            right.to_jobject(),
            pos.to_jobject()
        )
    }

    pub fn and(&self, left: Expr, right: Expr) -> Expr<'a> {
        self.and_with_pos(left, right, self.no_position())
    }

    pub fn implies_with_pos(&self, left: Expr, right: Expr, pos: Position) -> Expr<'a> {
        build_ast_node_with_pos!(
            self,
            Expr,
            ast::Implies,
            left.to_jobject(),
            right.to_jobject(),
            pos.to_jobject()
        )
    }

    pub fn implies(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::Implies,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn magic_wand_with_pos(&self, left: Expr, right: Expr, pos: Position) -> Expr<'a> {
        build_ast_node_with_pos!(
            self,
            Expr,
            ast::MagicWand,
            left.to_jobject(),
            right.to_jobject(),
            pos.to_jobject()
        )
    }

    pub fn magic_wand(&self, left: Expr, right: Expr) -> Expr<'a> {
        self.magic_wand_with_pos(left, right, self.no_position())
    }

    pub fn not_with_pos(&self, expr: Expr, pos: Position) -> Expr<'a> {
        build_ast_node_with_pos!(self, Expr, ast::Not, expr.to_jobject(), pos.to_jobject())
    }

    pub fn not(&self, expr: Expr) -> Expr<'a> {
        self.not_with_pos(expr, self.no_position())
    }

    pub fn true_lit_with_pos(&self, pos: Position) -> Expr<'a> {
        build_ast_node_with_pos!(self, Expr, ast::TrueLit, pos.to_jobject())
    }

    pub fn true_lit(&self) -> Expr<'a> {
        self.true_lit_with_pos(self.no_position())
    }

    pub fn false_lit_with_pos(&self, pos: Position) -> Expr<'a> {
        build_ast_node_with_pos!(self, Expr, ast::FalseLit, pos.to_jobject())
    }

    pub fn false_lit(&self) -> Expr<'a> {
        self.false_lit_with_pos(self.no_position())
    }

    pub fn null_lit_with_pos(&self, pos: Position) -> Expr<'a> {
        build_ast_node_with_pos!(self, Expr, ast::NullLit, pos.to_jobject())
    }

    pub fn null_lit(&self) -> Expr<'a> {
        self.null_lit_with_pos(self.no_position())
    }

    pub fn field_access_predicate_with_pos(
        &self,
        loc: Expr,
        perm: Expr,
        pos: Position,
    ) -> Expr<'a> {
        build_ast_node_with_pos!(
            self,
            Expr,
            ast::FieldAccessPredicate,
            loc.to_jobject(),
            perm.to_jobject(),
            pos.to_jobject()
        )
    }

    pub fn field_access_predicate(&self, loc: Expr, perm: Expr) -> Expr<'a> {
        self.field_access_predicate_with_pos(loc, perm, self.no_position())
    }

    pub fn predicate_access_predicate_with_pos(
        &self,
        loc: Expr,
        perm: Expr,
        pos: Position,
    ) -> Expr<'a> {
        build_ast_node_with_pos!(
            self,
            Expr,
            ast::PredicateAccessPredicate,
            loc.to_jobject(),
            perm.to_jobject(),
            pos.to_jobject()
        )
    }

    pub fn predicate_access_predicate(&self, loc: Expr, perm: Expr) -> Expr<'a> {
        self.predicate_access_predicate_with_pos(loc, perm, self.no_position())
    }

    pub fn inhale_exhale_pred(&self, inhale: Expr, exhale: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::InhaleExhaleExp,
            inhale.to_jobject(),
            exhale.to_jobject()
        )
    }

    pub fn wildcard_perm(&self) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::WildcardPerm)
    }

    pub fn full_perm(&self) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::FullPerm)
    }

    pub fn no_perm(&self) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::NoPerm)
    }

    pub fn epsilon_perm(&self) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::EpsilonPerm)
    }

    pub fn fractional_perm(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::FractionalPerm,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn perm_div(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::PermDiv,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn current_perm(&self, loc: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::CurrentPerm, loc.to_jobject())
    }

    pub fn perm_minus(&self, expr: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::PermMinus, expr.to_jobject())
    }

    pub fn perm_add(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::PermAdd,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn perm_sub(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::PermSub,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn perm_mul(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::PermMul,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn int_perm_mul(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::IntPermMul,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn perm_lt_cmp(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::PermLtCmp,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn perm_le_cmp(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::PermLeCmp,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn perm_gt_cmp(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::PermGtCmp,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn perm_ge_cmp(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::PermGeCmp,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn func_app(
        &self,
        function_name: &str,
        args: &[Expr],
        return_type: Type,
        pos: Position,
    ) -> Expr<'a> {
        let func_app_wrapper = ast::FuncApp::with(self.env);
        let obj = self.jni.unwrap_result(func_app_wrapper.call_apply(
            self.jni.new_string(function_name),
            self.jni.new_seq(&map_to_jobjects!(args)),
            pos.to_jobject(),
            self.no_info(),
            return_type.to_jobject(),
            self.no_trafos(),
        ));
        Expr::new(obj)
    }

    pub fn domain_func_app2(
        &self,
        function_name: &str,
        args: &[Expr],
        type_var_map: &[(Type, Type)],
        return_type: Type,
        domain_name: &str,
        pos: Position,
    ) -> Expr<'a> {
        let domain_func_app_wrapper = ast::DomainFuncApp::with(self.env);
        let obj = self.jni.unwrap_result(domain_func_app_wrapper.new(
            self.jni.new_string(function_name),
            self.jni.new_seq(&map_to_jobjects!(args)),
            self.jni.new_map(&map_to_jobject_pairs!(type_var_map)),
            pos.to_jobject(),
            self.no_info(),
            return_type.to_jobject(),
            self.jni.new_string(domain_name),
            self.no_trafos(),
        ));
        Expr::new(obj)
    }

    pub fn domain_func_app(
        &self,
        domain_func: DomainFunc,
        args: &[Expr],
        type_var_map: &[(Type, Type)],
    ) -> Expr<'a> {
        let domain_func_app_object_wrapper = ast::DomainFuncApp_object::with(self.env);
        let obj = self.jni.unwrap_result(
            domain_func_app_object_wrapper.call_apply(
                self.jni
                    .unwrap_result(domain_func_app_object_wrapper.singleton()),
                domain_func.to_jobject(),
                self.jni.new_seq(&map_to_jobjects!(args)),
                self.jni.new_map(&map_to_jobject_pairs!(type_var_map)),
                self.no_position().to_jobject(),
                self.no_info(),
                self.no_trafos(),
            ),
        );
        Expr::new(obj)
    }

    pub fn backend_func_app(
        &self,
        backend_function: JObject,
        args: &[Expr],
        pos: Position,
    ) -> Expr<'a> {
        let backendfunc_app_object_wrapper = ast::BackendFuncApp_object::with(self.env);
        let obj = self.jni.unwrap_result(
            backendfunc_app_object_wrapper.call_apply(
                self.jni
                    .unwrap_result(backendfunc_app_object_wrapper.singleton()),
                backend_function,
                self.jni.new_seq(&map_to_jobjects!(args)),
                pos.to_jobject(),
                self.no_info(),
                self.no_trafos(),
            ),
        );
        Expr::new(obj)
    }

    pub fn field_access_with_pos(&self, rcv: Expr, field: Field, pos: Position) -> Expr<'a> {
        build_ast_node_with_pos!(
            self,
            Expr,
            ast::FieldAccess,
            rcv.to_jobject(),
            field.to_jobject(),
            pos.to_jobject()
        )
    }

    pub fn field_access(&self, rcv: Expr, field: Field) -> Expr<'a> {
        self.field_access_with_pos(rcv, field, self.no_position())
    }

    pub fn predicate_access(&self, args: &[Expr], predicate_name: &str) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::PredicateAccess,
            self.jni.new_seq(&map_to_jobjects!(args)),
            self.jni.new_string(predicate_name)
        )
    }

    pub fn predicate_access_with_pos(
        &self,
        args: &[Expr],
        predicate_name: &str,
        pos: Position,
    ) -> Expr<'a> {
        build_ast_node_with_pos!(
            self,
            Expr,
            ast::PredicateAccess,
            self.jni.new_seq(&map_to_jobjects!(args)),
            self.jni.new_string(predicate_name),
            pos.to_jobject()
        )
    }

    pub fn cond_exp_with_pos(
        &self,
        cond: Expr,
        then_expr: Expr,
        else_expr: Expr,
        pos: Position,
    ) -> Expr<'a> {
        build_ast_node_with_pos!(
            self,
            Expr,
            ast::CondExp,
            cond.to_jobject(),
            then_expr.to_jobject(),
            else_expr.to_jobject(),
            pos.to_jobject()
        )
    }

    pub fn cond_exp(&self, cond: Expr, then_expr: Expr, else_expr: Expr) -> Expr<'a> {
        self.cond_exp_with_pos(cond, then_expr, else_expr, self.no_position())
    }

    pub fn unfolding_with_pos(&self, acc: Expr, body: Expr, pos: Position) -> Expr<'a> {
        build_ast_node_with_pos!(
            self,
            Expr,
            ast::Unfolding,
            acc.to_jobject(),
            body.to_jobject(),
            pos.to_jobject()
        )
    }

    pub fn unfolding(&self, acc: Expr, body: Expr) -> Expr<'a> {
        self.unfolding_with_pos(acc, body, self.no_position())
    }

    pub fn applying(&self, wand: Expr, body: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::Applying,
            wand.to_jobject(),
            body.to_jobject()
        )
    }

    pub fn old(&self, expr: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::Old, expr.to_jobject())
    }

    pub fn labelled_old_with_pos(&self, expr: Expr, old_label: &str, pos: Position) -> Expr<'a> {
        build_ast_node_with_pos!(
            self,
            Expr,
            ast::LabelledOld,
            expr.to_jobject(),
            self.jni.new_string(old_label),
            pos.to_jobject()
        )
    }

    pub fn labelled_old(&self, expr: Expr, old_label: &str) -> Expr<'a> {
        self.labelled_old_with_pos(expr, old_label, self.no_position())
    }

    pub fn let_expr_with_pos(
        &self,
        variable: LocalVarDecl,
        expr: Expr,
        body: Expr,
        pos: Position,
    ) -> Expr<'a> {
        build_ast_node_with_pos!(
            self,
            Expr,
            ast::Let,
            variable.to_jobject(),
            expr.to_jobject(),
            body.to_jobject(),
            pos.to_jobject()
        )
    }

    pub fn let_expr(&self, variable: LocalVarDecl, expr: Expr, body: Expr) -> Expr<'a> {
        self.let_expr_with_pos(variable, expr, body, self.no_position())
    }

    pub fn forall_with_pos(
        &self,
        variables: &[LocalVarDecl],
        triggers: &[Trigger],
        expr: Expr,
        pos: Position,
    ) -> Expr<'a> {
        build_ast_node_with_pos!(
            self,
            Expr,
            ast::Forall,
            self.jni.new_seq(&map_to_jobjects!(variables)),
            self.jni.new_seq(&map_to_jobjects!(triggers)),
            expr.to_jobject(),
            pos.to_jobject()
        )
    }

    pub fn forall(&self, variables: &[LocalVarDecl], triggers: &[Trigger], expr: Expr) -> Expr<'a> {
        self.forall_with_pos(variables, triggers, expr, self.no_position())
    }

    pub fn exists_with_pos(
        &self,
        variables: &[LocalVarDecl],
        triggers: &[Trigger],
        expr: Expr,
        _pos: Position, // FIXME: Why???
    ) -> Expr<'a> {
        build_ast_node_with_pos!(
            self,
            Expr,
            ast::Exists,
            self.jni.new_seq(&map_to_jobjects!(variables)),
            self.jni.new_seq(&map_to_jobjects!(triggers)),
            expr.to_jobject(),
            self.no_position().to_jobject()
        )
    }

    pub fn exists(&self, variables: &[LocalVarDecl], triggers: &[Trigger], expr: Expr) -> Expr<'a> {
        self.exists_with_pos(variables, triggers, expr, self.no_position())
    }

    pub fn for_perm(
        &self,
        variable: LocalVarDecl,
        access_list: &[Location],
        body: Expr,
    ) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::ForPerm,
            variable.to_jobject(),
            self.jni.new_seq(&map_to_jobjects!(access_list)),
            body.to_jobject()
        )
    }

    pub fn trigger_with_pos(&self, exps: &[Expr], pos: Position) -> Trigger<'a> {
        build_ast_node_with_pos!(
            self,
            Trigger,
            ast::Trigger,
            self.jni.new_seq(&map_to_jobjects!(exps)),
            pos.to_jobject()
        )
    }

    pub fn trigger(&self, exps: &[Expr]) -> Trigger<'a> {
        self.trigger_with_pos(exps, self.no_position())
    }

    pub fn local_var_with_pos(&self, name: &str, var_type: Type, pos: Position) -> Expr<'a> {
        build_ast_node_with_pos!(
            self,
            Expr,
            ast::LocalVar,
            self.jni.new_string(name),
            var_type.to_jobject(),
            pos.to_jobject()
        )
    }

    pub fn local_var(&self, name: &str, var_type: Type) -> Expr<'a> {
        self.local_var_with_pos(name, var_type, self.no_position())
    }

    pub fn result_with_pos(&self, var_type: Type, pos: Position) -> Expr<'a> {
        build_ast_node_with_pos!(
            self,
            Expr,
            ast::Result,
            var_type.to_jobject(),
            pos.to_jobject()
        )
    }

    pub fn empty_seq(&self, elem_type: Type) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::EmptySeq, elem_type.to_jobject())
    }

    pub fn explicit_seq(&self, elems: &[Expr]) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::ExplicitSeq,
            self.jni.new_seq(&map_to_jobjects!(elems))
        )
    }

    pub fn empty_map(&self, key_ty: Type, val_ty: Type) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::EmptyMap,
            key_ty.to_jobject(),
            val_ty.to_jobject()
        )
    }

    pub fn explicit_map(&self, keys_values: &[Expr]) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::ExplicitMap,
            self.jni.new_seq(&map_to_jobjects!(keys_values))
        )
    }

    pub fn update_map(&self, map: Expr, key: Expr, val: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::MapUpdate,
            map.to_jobject(),
            key.to_jobject(),
            val.to_jobject()
        )
    }

    pub fn lookup_map(&self, map: Expr, key: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::MapLookup,
            map.to_jobject(),
            key.to_jobject()
        )
    }

    pub fn map_contains(&self, map: Expr, key: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::MapContains,
            key.to_jobject(),
            map.to_jobject()
        )
    }

    pub fn map_len(&self, map: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::MapCardinality, map.to_jobject())
    }

    pub fn range_seq(&self, low: Expr, high: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::RangeSeq,
            low.to_jobject(),
            high.to_jobject()
        )
    }

    pub fn seq_append(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::SeqAppend,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn seq_index(&self, seq: Expr, index: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::SeqIndex,
            seq.to_jobject(),
            index.to_jobject()
        )
    }

    pub fn seq_take(&self, seq: Expr, num: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::SeqTake, seq.to_jobject(), num.to_jobject())
    }

    pub fn seq_drop(&self, seq: Expr, num: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::SeqDrop, seq.to_jobject(), num.to_jobject())
    }

    pub fn seq_contains(&self, elem: Expr, seq: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::SeqContains,
            elem.to_jobject(),
            seq.to_jobject()
        )
    }

    pub fn seq_update(&self, seq: Expr, index: Expr, elem: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::SeqUpdate,
            seq.to_jobject(),
            index.to_jobject(),
            elem.to_jobject()
        )
    }

    pub fn seq_length(&self, seq: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::SeqLength, seq.to_jobject())
    }

    pub fn empty_set(&self, elem_type: Type) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::EmptySet, elem_type.to_jobject())
    }

    pub fn explicit_set(&self, elems: &[Expr]) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::ExplicitSet,
            self.jni.new_seq(&map_to_jobjects!(elems))
        )
    }

    pub fn empty_multiset(&self, elem_type: Type) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::EmptyMultiset, elem_type.to_jobject())
    }

    pub fn explicit_multiset(&self, elems: &[Expr]) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::ExplicitMultiset,
            self.jni.new_seq(&map_to_jobjects!(elems))
        )
    }

    pub fn any_set_union(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::AnySetUnion,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn any_set_intersection(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::AnySetIntersection,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn any_set_subset(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::AnySetSubset,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn any_set_minus(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::AnySetMinus,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn any_set_contains(&self, elem: Expr, set: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::AnySetContains,
            elem.to_jobject(),
            set.to_jobject()
        )
    }

    pub fn any_set_cardinality(&self, set: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::AnySetCardinality, set.to_jobject())
    }

    pub fn simplified_expression(&self, expr: Expr) -> Expr<'a> {
        let simplifier_object_wrapper = ast::utility::Simplifier_object::with(self.env);
        let obj = self.jni.unwrap_result(
            simplifier_object_wrapper.call_simplify(
                self.jni
                    .unwrap_result(simplifier_object_wrapper.singleton()),
                expr.to_jobject(),
            ),
        );
        Expr::new(obj)
    }
}
