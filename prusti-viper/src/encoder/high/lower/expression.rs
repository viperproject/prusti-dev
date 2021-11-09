use super::super::types::interface::HighTypeEncoderInterfacePrivate;

use super::IntoPolymorphic;
use vir_crate::{high as vir_high, polymorphic as vir_poly};

impl IntoPolymorphic<Box<vir_poly::Expr>> for Box<vir_high::Expression> {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> Box<vir_poly::Expr> {
        Box::new((**self).lower(encoder))
    }
}

impl IntoPolymorphic<Vec<vir_poly::Expr>> for Vec<vir_high::Expression> {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> Vec<vir_poly::Expr> {
        self.iter().map(|element| element.lower(encoder)).collect()
    }
}

impl IntoPolymorphic<vir_poly::Expr> for vir_high::Expression {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::Expr {
        match self {
            vir_high::Expression::Local(expression) => {
                vir_poly::Expr::Local(expression.lower(encoder))
            }
            vir_high::Expression::Constructor(expression) => {
                unimplemented!("not supported lowering: {}", expression);
            }
            vir_high::Expression::Variant(expression) => {
                vir_poly::Expr::Variant(expression.lower(encoder))
            }
            vir_high::Expression::Field(expression) => {
                vir_poly::Expr::Field(expression.lower(encoder))
            }
            vir_high::Expression::Deref(expression) => {
                vir_poly::Expr::Field(expression.lower(encoder))
            }
            vir_high::Expression::AddrOf(expression) => {
                vir_poly::Expr::AddrOf(expression.lower(encoder))
            }
            vir_high::Expression::LabelledOld(expression) => {
                vir_poly::Expr::LabelledOld(expression.lower(encoder))
            }
            vir_high::Expression::Constant(expression) => {
                vir_poly::Expr::Const(expression.lower(encoder))
            }
            vir_high::Expression::UnaryOp(expression) => {
                vir_poly::Expr::UnaryOp(expression.lower(encoder))
            }
            vir_high::Expression::BinOp(expression) => {
                vir_poly::Expr::BinOp(expression.lower(encoder))
            }
            vir_high::Expression::ContainerOp(expression) => {
                vir_poly::Expr::ContainerOp(expression.lower(encoder))
            }
            vir_high::Expression::Seq(expression) => vir_poly::Expr::Seq(expression.lower(encoder)),
            vir_high::Expression::Conditional(expression) => {
                vir_poly::Expr::Cond(expression.lower(encoder))
            }
            vir_high::Expression::Quantifier(expression) => match expression.kind {
                vir_high::expression::QuantifierKind::ForAll => {
                    vir_poly::Expr::ForAll(expression.lower(encoder))
                }
                vir_high::expression::QuantifierKind::Exists => {
                    vir_poly::Expr::Exists(expression.lower(encoder))
                }
            },
            vir_high::Expression::LetExpr(expression) => {
                vir_poly::Expr::LetExpr(expression.lower(encoder))
            }
            vir_high::Expression::FuncApp(expression) => {
                vir_poly::Expr::FuncApp(expression.lower(encoder))
            }
            vir_high::Expression::Downcast(expression) => {
                vir_poly::Expr::Downcast(expression.lower(encoder))
            }
        }
    }
}

impl IntoPolymorphic<vir_poly::Local> for vir_high::expression::Local {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::Local {
        vir_poly::Local {
            variable: self.variable.lower(encoder),
            position: self.position.lower(encoder),
        }
    }
}

impl IntoPolymorphic<vir_poly::Variant> for vir_high::expression::Variant {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::Variant {
        vir_poly::Variant {
            base: self.base.lower(encoder),
            variant_index: vir_poly::Field::new(
                self.variant_index.to_string(),
                self.ty.lower(encoder),
            ),
            position: self.position.lower(encoder),
        }
    }
}

impl IntoPolymorphic<vir_poly::FieldExpr> for vir_high::expression::Field {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::FieldExpr {
        vir_poly::FieldExpr {
            base: self.base.lower(encoder),
            field: self.field.lower(encoder),
            position: self.position.lower(encoder),
        }
    }
}

impl IntoPolymorphic<vir_poly::FieldExpr> for vir_high::expression::Deref {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::FieldExpr {
        vir_poly::FieldExpr {
            base: self.base.lower(encoder),
            field: vir_poly::Field::new("val_ref", self.ty.lower(encoder)),
            position: self.position.lower(encoder),
        }
    }
}

impl IntoPolymorphic<vir_poly::AddrOf> for vir_high::expression::AddrOf {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::AddrOf {
        vir_poly::AddrOf {
            base: self.base.lower(encoder),
            addr_type: self.ty.lower(encoder),
            position: self.position.lower(encoder),
        }
    }
}

impl IntoPolymorphic<vir_poly::LabelledOld> for vir_high::expression::LabelledOld {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::LabelledOld {
        vir_poly::LabelledOld {
            label: self.label.clone(),
            base: self.base.lower(encoder),
            position: self.position.lower(encoder),
        }
    }
}

impl IntoPolymorphic<vir_poly::ConstExpr> for vir_high::expression::Constant {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::ConstExpr {
        vir_poly::ConstExpr {
            value: self.value.lower(encoder),
            position: self.position.lower(encoder),
        }
    }
}

impl IntoPolymorphic<vir_poly::Const> for vir_high::expression::ConstantValue {
    fn lower(&self, _encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::Const {
        match self {
            vir_high::expression::ConstantValue::Bool(value) => vir_poly::Const::Bool(*value),
            vir_high::expression::ConstantValue::Int(value) => vir_poly::Const::Int(*value),
            vir_high::expression::ConstantValue::BigInt(value) => {
                vir_poly::Const::BigInt(value.clone())
            }
            vir_high::expression::ConstantValue::FnPtr => vir_poly::Const::FnPtr,
        }
    }
}

impl IntoPolymorphic<vir_poly::UnaryOp> for vir_high::expression::UnaryOp {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::UnaryOp {
        vir_poly::UnaryOp {
            op_kind: self.op_kind.lower(encoder),
            argument: self.argument.lower(encoder),
            position: self.position.lower(encoder),
        }
    }
}

impl IntoPolymorphic<vir_poly::UnaryOpKind> for vir_high::expression::UnaryOpKind {
    fn lower(&self, _encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::UnaryOpKind {
        match self {
            vir_high::expression::UnaryOpKind::Not => vir_poly::UnaryOpKind::Not,
            vir_high::expression::UnaryOpKind::Minus => vir_poly::UnaryOpKind::Minus,
        }
    }
}

impl IntoPolymorphic<vir_poly::BinOp> for vir_high::expression::BinOp {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::BinOp {
        vir_poly::BinOp {
            op_kind: self.op_kind.lower(encoder),
            left: self.left.lower(encoder),
            right: self.right.lower(encoder),
            position: self.position.lower(encoder),
        }
    }
}

impl IntoPolymorphic<vir_poly::BinaryOpKind> for vir_high::expression::BinaryOpKind {
    fn lower(&self, _encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::BinaryOpKind {
        match self {
            vir_high::expression::BinaryOpKind::EqCmp => vir_poly::BinaryOpKind::EqCmp,
            vir_high::expression::BinaryOpKind::NeCmp => vir_poly::BinaryOpKind::NeCmp,
            vir_high::expression::BinaryOpKind::GtCmp => vir_poly::BinaryOpKind::GtCmp,
            vir_high::expression::BinaryOpKind::GeCmp => vir_poly::BinaryOpKind::GeCmp,
            vir_high::expression::BinaryOpKind::LtCmp => vir_poly::BinaryOpKind::LtCmp,
            vir_high::expression::BinaryOpKind::LeCmp => vir_poly::BinaryOpKind::LeCmp,
            vir_high::expression::BinaryOpKind::Add => vir_poly::BinaryOpKind::Add,
            vir_high::expression::BinaryOpKind::Sub => vir_poly::BinaryOpKind::Sub,
            vir_high::expression::BinaryOpKind::Mul => vir_poly::BinaryOpKind::Mul,
            vir_high::expression::BinaryOpKind::Div => vir_poly::BinaryOpKind::Div,
            vir_high::expression::BinaryOpKind::Mod => vir_poly::BinaryOpKind::Mod,
            vir_high::expression::BinaryOpKind::And => vir_poly::BinaryOpKind::And,
            vir_high::expression::BinaryOpKind::Or => vir_poly::BinaryOpKind::Or,
            vir_high::expression::BinaryOpKind::Implies => vir_poly::BinaryOpKind::Implies,
        }
    }
}

impl IntoPolymorphic<vir_poly::ContainerOp> for vir_high::expression::ContainerOp {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::ContainerOp {
        vir_poly::ContainerOp {
            op_kind: self.op_kind.lower(encoder),
            left: self.left.lower(encoder),
            right: self.right.lower(encoder),
            position: self.position.lower(encoder),
        }
    }
}

impl IntoPolymorphic<vir_poly::ContainerOpKind> for vir_high::expression::ContainerOpKind {
    fn lower(&self, _encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::ContainerOpKind {
        match self {
            vir_high::expression::ContainerOpKind::SeqIndex => vir_poly::ContainerOpKind::SeqIndex,
            vir_high::expression::ContainerOpKind::SeqConcat => {
                vir_poly::ContainerOpKind::SeqConcat
            }
            vir_high::expression::ContainerOpKind::SeqLen => vir_poly::ContainerOpKind::SeqLen,
        }
    }
}

impl IntoPolymorphic<vir_poly::Seq> for vir_high::expression::Seq {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::Seq {
        vir_poly::Seq {
            typ: self.ty.lower(encoder),
            elements: self.elements.lower(encoder),
            position: self.position.lower(encoder),
        }
    }
}

impl IntoPolymorphic<vir_poly::Cond> for vir_high::expression::Conditional {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::Cond {
        vir_poly::Cond {
            guard: self.guard.lower(encoder),
            then_expr: self.then_expr.lower(encoder),
            else_expr: self.else_expr.lower(encoder),
            position: self.position.lower(encoder),
        }
    }
}

impl IntoPolymorphic<vir_poly::ForAll> for vir_high::expression::Quantifier {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::ForAll {
        assert_eq!(self.kind, vir_high::expression::QuantifierKind::ForAll);
        vir_poly::ForAll {
            variables: self.variables.lower(encoder),
            triggers: self.triggers.lower(encoder),
            body: self.body.lower(encoder),
            position: self.position.lower(encoder),
        }
    }
}

impl IntoPolymorphic<vir_poly::Exists> for vir_high::expression::Quantifier {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::Exists {
        assert_eq!(self.kind, vir_high::expression::QuantifierKind::Exists);
        vir_poly::Exists {
            variables: self.variables.lower(encoder),
            triggers: self.triggers.lower(encoder),
            body: self.body.lower(encoder),
            position: self.position.lower(encoder),
        }
    }
}

impl IntoPolymorphic<vir_poly::Trigger> for vir_high::expression::Trigger {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::Trigger {
        vir_poly::Trigger::new(self.terms.lower(encoder))
    }
}

impl IntoPolymorphic<Vec<vir_poly::Trigger>> for Vec<vir_high::expression::Trigger> {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> Vec<vir_poly::Trigger> {
        self.iter().map(|trigger| trigger.lower(encoder)).collect()
    }
}

impl IntoPolymorphic<vir_poly::LetExpr> for vir_high::expression::LetExpr {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::LetExpr {
        vir_poly::LetExpr {
            variable: self.variable.lower(encoder),
            def: self.def.lower(encoder),
            body: self.body.lower(encoder),
            position: self.position.lower(encoder),
        }
    }
}

impl IntoPolymorphic<vir_poly::FuncApp> for vir_high::expression::FuncApp {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::FuncApp {
        vir_poly::FuncApp {
            function_name: self.function_name.clone(),
            arguments: self.arguments.lower(encoder),
            formal_arguments: self.parameters.lower(encoder),
            return_type: self.return_type.lower(encoder),
            position: self.position.lower(encoder),
        }
    }
}

impl IntoPolymorphic<vir_poly::DowncastExpr> for vir_high::expression::Downcast {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> vir_poly::DowncastExpr {
        vir_poly::DowncastExpr {
            base: self.base.lower(encoder),
            enum_place: self.enum_place.lower(encoder),
            field: self.field.lower(encoder),
        }
    }
}
