//! If the program uses bit operations, change all integers to bitvectors.

use vir::polymorphic::{self as vir_poly, ExprFolder, ExprWalker, StmtFolder, StmtWalker};

pub fn uses_bit_operations(program: &vir_poly::Program) -> bool {
    let mut checker = Checker {
        uses_bit_operations: false,
    };
    vir_poly::walk_methods(&program.methods, &mut checker);
    checker.uses_bit_operations
}

struct Checker {
    uses_bit_operations: bool,
}

impl ExprWalker for Checker {
    fn walk_bin_op(&mut self, expr: &vir_poly::BinOp) {
        use vir_poly::BinaryOpKind::*;
        if matches!(
            expr.op_kind,
            BitAnd | BitOr | BitXor | Shl | LShr | AShr | Min | Max
        ) {
            self.uses_bit_operations = true;
        }
        ExprWalker::walk(self, &expr.left);
        ExprWalker::walk(self, &expr.right);
    }
}

impl StmtWalker for Checker {
    fn walk_expr(&mut self, expr: &vir_poly::Expr) {
        ExprWalker::walk(self, expr)
    }
}

pub fn replace_all_ints(program: &mut vir_poly::Program) {
    let mut replacer = Replacer { captured_bv: None };
    let mut sentinel_stmt = vir_poly::Stmt::comment("moved out stmt");
    for method in &mut program.methods {
        for block in &mut method.basic_blocks {
            for stmt in &mut block.stmts {
                std::mem::swap(&mut sentinel_stmt, stmt);
                replacer.captured_bv = None;
                sentinel_stmt = StmtFolder::fold(&mut replacer, sentinel_stmt);
                std::mem::swap(&mut sentinel_stmt, stmt);
            }
        }
    }
    for predicate in &mut program.viper_predicates {
        match predicate {
            vir_poly::Predicate::Struct(predicate) => {
                if let Some(body) = predicate.body.take() {
                    replacer.captured_bv = None;
                    let body = ExprFolder::fold(&mut replacer, body);
                    predicate.body = Some(body);
                }
            }
            vir_poly::Predicate::Enum(predicate) => {
                for (_, _, variant) in &mut predicate.variants {
                    replacer.captured_bv = None;
                    if let Some(body) = variant.body.take() {
                        let body = ExprFolder::fold(&mut replacer, body);
                        variant.body = Some(body);
                    }
                }
            }
            vir_poly::Predicate::Bodyless(..) => {}
        }
    }
    program.fields.extend(vec![
        vir_poly::Field::new(
            "field_bv8",
            vir_poly::Type::BitVector(vir_poly::BitVector::BV8),
        ),
        vir_poly::Field::new(
            "field_bv16",
            vir_poly::Type::BitVector(vir_poly::BitVector::BV16),
        ),
        vir_poly::Field::new(
            "field_bv32",
            vir_poly::Type::BitVector(vir_poly::BitVector::BV32),
        ),
        vir_poly::Field::new(
            "field_bv64",
            vir_poly::Type::BitVector(vir_poly::BitVector::BV64),
        ),
        vir_poly::Field::new(
            "field_bv128",
            vir_poly::Type::BitVector(vir_poly::BitVector::BV128),
        ),
    ]);
}

struct Replacer {
    captured_bv: Option<vir_poly::BitVector>,
}

impl ExprFolder for Replacer {
    fn fold_field(&mut self, mut expr: vir_poly::FieldExpr) -> vir_poly::Expr {
        if let vir_poly::Type::TypedRef(vir_poly::TypedRef { label, .. }) = expr.base.get_type() {
            match label.as_ref() {
                "u8" | "i8" => {
                    let variant = vir_poly::BitVector::BV8;
                    self.captured_bv = Some(variant);
                    expr.field =
                        vir_poly::Field::new("field_bv8", vir_poly::Type::BitVector(variant))
                }
                "u16" | "i16" => {
                    let variant = vir_poly::BitVector::BV16;
                    self.captured_bv = Some(variant);
                    expr.field =
                        vir_poly::Field::new("field_bv16", vir_poly::Type::BitVector(variant))
                }
                "u32" | "i32" => {
                    let variant = vir_poly::BitVector::BV32;
                    self.captured_bv = Some(variant);
                    expr.field =
                        vir_poly::Field::new("field_bv32", vir_poly::Type::BitVector(variant))
                }
                "u64" | "i64" => {
                    let variant = vir_poly::BitVector::BV64;
                    self.captured_bv = Some(variant);
                    expr.field =
                        vir_poly::Field::new("field_bv64", vir_poly::Type::BitVector(variant))
                }
                "u128" | "i128" => {
                    let variant = vir_poly::BitVector::BV128;
                    self.captured_bv = Some(variant);
                    expr.field =
                        vir_poly::Field::new("field_bv128", vir_poly::Type::BitVector(variant))
                }
                _ => {}
            };
        }
        vir_poly::Expr::Field(expr)
    }
    fn fold_const(&mut self, mut expr: vir_poly::ConstExpr) -> vir_poly::Expr {
        match &expr.value {
            vir_poly::Const::Int(value) => {
                let value = *value;
                if let Some(captured_bv) = &self.captured_bv {
                    let const_value = match captured_bv {
                        vir_poly::BitVector::BV8 => vir_poly::BitVectorConst::BV8(value as u8),
                        vir_poly::BitVector::BV16 => vir_poly::BitVectorConst::BV16(value as u16),
                        vir_poly::BitVector::BV32 => vir_poly::BitVectorConst::BV32(value as u32),
                        vir_poly::BitVector::BV64 => vir_poly::BitVectorConst::BV64(value as u64),
                        vir_poly::BitVector::BV128 => {
                            vir_poly::BitVectorConst::BV128(value as u128)
                        }
                    };
                    expr.value = vir_poly::Const::BitVector(const_value);
                }
            }
            vir_poly::Const::BigInt(_value) => {
                unimplemented!()
            }
            _ => {}
        };
        vir_poly::Expr::Const(expr)
    }
}

impl StmtFolder for Replacer {
    fn fold_expr(&mut self, expr: vir_poly::Expr) -> vir_poly::Expr {
        ExprFolder::fold(self, expr)
    }
}
