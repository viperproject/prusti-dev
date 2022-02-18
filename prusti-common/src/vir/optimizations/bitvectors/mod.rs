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
                    let body = ExprFolder::fold(&mut Fixer, body);
                    predicate.body = Some(body);
                }
            }
            vir_poly::Predicate::Enum(predicate) => {
                for (_, _, variant) in &mut predicate.variants {
                    replacer.captured_bv = None;
                    if let Some(body) = variant.body.take() {
                        let body = ExprFolder::fold(&mut replacer, body);
                        let body = ExprFolder::fold(&mut Fixer, body);
                        variant.body = Some(body);
                    }
                }
            }
            vir_poly::Predicate::Bodyless(..) => {}
        }
    }
    let types = [
        vir_poly::BitVectorSize::BV8,
        vir_poly::BitVectorSize::BV16,
        vir_poly::BitVectorSize::BV32,
        vir_poly::BitVectorSize::BV64,
        vir_poly::BitVectorSize::BV128,
    ];
    for typ in types {
        let signed = vir_poly::BitVector::Signed(typ);
        let unsigned = vir_poly::BitVector::Unsigned(typ);
        program.fields.push(vir_poly::Field::new(
            format!("field_{}", signed),
            vir_poly::Type::BitVector(signed),
        ));
        program.fields.push(vir_poly::Field::new(
            format!("field_{}", unsigned),
            vir_poly::Type::BitVector(unsigned),
        ));
    }
}

struct Replacer {
    captured_bv: Option<vir_poly::BitVector>,
}

impl ExprFolder for Replacer {
    fn fold_field(&mut self, mut expr: vir_poly::FieldExpr) -> vir_poly::Expr {
        if let vir_poly::Type::TypedRef(vir_poly::TypedRef { label, .. }) = expr.base.get_type() {
            let variant = match label.as_ref() {
                "u8" => Some(vir_poly::BitVector::Unsigned(vir_poly::BitVectorSize::BV8)),
                "u16" => Some(vir_poly::BitVector::Unsigned(vir_poly::BitVectorSize::BV16)),
                "u32" => Some(vir_poly::BitVector::Unsigned(vir_poly::BitVectorSize::BV32)),
                "u64" => Some(vir_poly::BitVector::Unsigned(vir_poly::BitVectorSize::BV64)),
                "u128" => Some(vir_poly::BitVector::Unsigned(
                    vir_poly::BitVectorSize::BV128,
                )),
                "i8" => Some(vir_poly::BitVector::Signed(vir_poly::BitVectorSize::BV8)),
                "i16" => Some(vir_poly::BitVector::Signed(vir_poly::BitVectorSize::BV16)),
                "i32" => Some(vir_poly::BitVector::Signed(vir_poly::BitVectorSize::BV32)),
                "i64" => Some(vir_poly::BitVector::Signed(vir_poly::BitVectorSize::BV64)),
                "i128" => Some(vir_poly::BitVector::Signed(vir_poly::BitVectorSize::BV128)),
                _ => None,
            };
            if let Some(variant) = variant {
                self.captured_bv = Some(variant);
                expr.field = vir_poly::Field::new(
                    format!("field_{}", variant),
                    vir_poly::Type::BitVector(variant),
                )
            }
        }
        vir_poly::Expr::Field(expr)
    }
    fn fold_const(&mut self, mut expr: vir_poly::ConstExpr) -> vir_poly::Expr {
        match &expr.value {
            vir_poly::Const::Int(value) => {
                let value = *value;
                if let Some(captured_bv) = &self.captured_bv {
                    let const_value = vir_poly::BitVectorConst {
                        value: value.to_string(),
                        typ: *captured_bv,
                    };
                    expr.value = vir_poly::Const::BitVector(const_value);
                }
            }
            vir_poly::Const::BigInt(_value) => {
                // if let Some(captured_bv) = &self.captured_bv {
                //     let const_value = match captured_bv {
                //         vir_poly::BitVector::BV8 => vir_poly::BitVectorConst::BV8(value.parse::<u8>().unwrap()),
                //         vir_poly::BitVector::BV16 => vir_poly::BitVectorConst::BV16(value.parse::<u16>().unwrap()),
                //         vir_poly::BitVector::BV32 => vir_poly::BitVectorConst::BV32(value.parse::<u32>().unwrap()),
                //         vir_poly::BitVector::BV64 => vir_poly::BitVectorConst::BV64(value.parse::<u64>().unwrap()),
                //         vir_poly::BitVector::BV128 => {
                //             vir_poly::BitVectorConst::BV128(value.parse::<u128>().unwrap())
                //         }
                //     };
                //     expr.value = vir_poly::Const::BitVector(const_value);
                // }
            }
            _ => {}
        };
        vir_poly::Expr::Const(expr)
    }
}

impl StmtFolder for Replacer {
    fn fold_expr(&mut self, expr: vir_poly::Expr) -> vir_poly::Expr {
        let expr = ExprFolder::fold(self, expr);
        ExprFolder::fold(&mut Fixer, expr)
    }
}

struct Fixer;

impl ExprFolder for Fixer {
    fn fold_bin_op(
        &mut self,
        vir_poly::BinOp {
            op_kind,
            mut left,
            mut right,
            position,
        }: vir_poly::BinOp,
    ) -> vir_poly::Expr {
        left = self.fold_boxed(left);
        right = self.fold_boxed(right);
        if op_kind != vir_poly::BinaryOpKind::And {
            let left_type = left.get_type();
            let right_type = right.get_type();
            if left_type != right_type {
                match op_kind {
                    vir_poly::BinaryOpKind::EqCmp
                    | vir_poly::BinaryOpKind::NeCmp
                    | vir_poly::BinaryOpKind::GtCmp
                    | vir_poly::BinaryOpKind::GeCmp
                    | vir_poly::BinaryOpKind::LtCmp
                    | vir_poly::BinaryOpKind::LeCmp
                    | vir_poly::BinaryOpKind::Add
                    | vir_poly::BinaryOpKind::Sub
                    | vir_poly::BinaryOpKind::Mul
                    | vir_poly::BinaryOpKind::Div
                    | vir_poly::BinaryOpKind::Mod => {
                        (left, right) = ensure_int(left, right);
                    }
                    vir_poly::BinaryOpKind::And
                    | vir_poly::BinaryOpKind::Or
                    | vir_poly::BinaryOpKind::Implies => {
                        unreachable!();
                    }
                    vir_poly::BinaryOpKind::BitAnd
                    | vir_poly::BinaryOpKind::BitOr
                    | vir_poly::BinaryOpKind::BitXor
                    | vir_poly::BinaryOpKind::Shl
                    | vir_poly::BinaryOpKind::LShr
                    | vir_poly::BinaryOpKind::AShr
                    | vir_poly::BinaryOpKind::Min
                    | vir_poly::BinaryOpKind::Max => {
                        (left, right) = ensure_bitvector(left, right);
                    }
                }
            }
        }
        vir_poly::Expr::BinOp(vir_poly::BinOp {
            op_kind,
            left,
            right,
            position,
        })
    }
}

fn ensure_int(
    mut left: Box<vir_poly::Expr>,
    mut right: Box<vir_poly::Expr>,
) -> (Box<vir_poly::Expr>, Box<vir_poly::Expr>) {
    if let vir_poly::Type::BitVector(size) = left.get_type() {
        left = Box::new(vir_poly::Expr::Cast(vir_poly::Cast {
            kind: vir_poly::CastKind::BVIntoInt(*size),
            position: left.pos(),
            base: left,
        }));
    }
    if let vir_poly::Type::BitVector(size) = right.get_type() {
        right = Box::new(vir_poly::Expr::Cast(vir_poly::Cast {
            kind: vir_poly::CastKind::BVIntoInt(*size),
            position: right.pos(),
            base: right,
        }));
    }
    (left, right)
}

fn ensure_bitvector(
    mut left: Box<vir_poly::Expr>,
    mut right: Box<vir_poly::Expr>,
) -> (Box<vir_poly::Expr>, Box<vir_poly::Expr>) {
    if let vir_poly::Type::BitVector(size) = right.get_type() {
        left = Box::new(vir_poly::Expr::Cast(vir_poly::Cast {
            kind: vir_poly::CastKind::IntIntoBV(*size),
            position: left.pos(),
            base: left,
        }));
    }
    if let vir_poly::Type::BitVector(size) = left.get_type() {
        right = Box::new(vir_poly::Expr::Cast(vir_poly::Cast {
            kind: vir_poly::CastKind::IntIntoBV(*size),
            position: right.pos(),
            base: right,
        }));
    }
    (left, right)
}
