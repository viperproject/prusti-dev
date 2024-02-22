use super::{
    super::super::transformations::{
        encoder_context::EncoderContext, predicate_domains::PredicateDomainsInfo,
        symbolic_execution_new::ProgramContext,
    },
    solver::Info,
    types::Type2Smt,
};
use rsmt2::{print::Expr2Smt, SmtRes};
use std::io::Write;
use vir_crate::low::{self as vir_low, operations::ty::Typed};

trait Expression2Smt<'a, Info> {
    fn expression_to_smt2<Writer>(&'a self, writer: &mut Writer, info: Info) -> SmtRes<()>
    where
        Writer: Write;
}

impl<'a, 'c, EC: EncoderContext, T> Expression2Smt<'a, Info<'a, 'c, EC>> for T
where
    Expr2SmtWrapper<'a, T>: Expr2Smt<Info<'a, 'c, EC>> + 'a,
{
    fn expression_to_smt2<Writer>(
        &'a self,
        writer: &mut Writer,
        info: Info<'a, 'c, EC>,
    ) -> SmtRes<()>
    where
        Writer: Write,
    {
        Expr2SmtWrapper::new(self).expr_to_smt2(writer, info)
    }
}

pub(super) struct Expr2SmtWrapper<'a, T> {
    expr: &'a T,
}

impl<'a, T> Expr2SmtWrapper<'a, T> {
    pub(super) fn new(expr: &'a T) -> Self {
        Self { expr }
    }
}

pub(super) trait Expr2SmtWrap<T> {
    fn wrap(&self) -> Expr2SmtWrapper<T>;
}

impl<'a> Expr2SmtWrap<vir_low::Expression> for vir_low::Expression {
    fn wrap(&self) -> Expr2SmtWrapper<vir_low::Expression> {
        Expr2SmtWrapper { expr: self }
    }
}

impl<'a, 'c, EC: EncoderContext> Expr2Smt<Info<'a, 'c, EC>>
    for Expr2SmtWrapper<'a, vir_low::Expression>
{
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: Info<'a, 'c, EC>) -> SmtRes<()>
    where
        Writer: Write,
    {
        match self.expr {
            vir_low::Expression::Local(expression) => expression.expression_to_smt2(writer, info),
            vir_low::Expression::Field(expression) => expression.expression_to_smt2(writer, info),
            vir_low::Expression::LabelledOld(expression) => {
                expression.expression_to_smt2(writer, info)
            }
            vir_low::Expression::Constant(expression) => {
                expression.expression_to_smt2(writer, info)
            }
            vir_low::Expression::MagicWand(expression) => {
                expression.expression_to_smt2(writer, info)
            }
            vir_low::Expression::PredicateAccessPredicate(expression) => {
                expression.expression_to_smt2(writer, info)
            }
            vir_low::Expression::FieldAccessPredicate(expression) => {
                expression.expression_to_smt2(writer, info)
            }
            vir_low::Expression::Unfolding(expression) => {
                expression.expression_to_smt2(writer, info)
            }
            vir_low::Expression::UnaryOp(expression) => expression.expression_to_smt2(writer, info),
            vir_low::Expression::BinaryOp(expression) => {
                expression.expression_to_smt2(writer, info)
            }
            vir_low::Expression::PermBinaryOp(expression) => {
                expression.expression_to_smt2(writer, info)
            }
            vir_low::Expression::ContainerOp(expression) => {
                expression.expression_to_smt2(writer, info)
            }
            vir_low::Expression::Conditional(expression) => {
                expression.expression_to_smt2(writer, info)
            }
            vir_low::Expression::Quantifier(expression) => {
                expression.expression_to_smt2(writer, info)
            }
            vir_low::Expression::LetExpr(expression) => expression.expression_to_smt2(writer, info),
            vir_low::Expression::FuncApp(expression) => expression.expression_to_smt2(writer, info),
            vir_low::Expression::DomainFuncApp(expression) => {
                expression.expression_to_smt2(writer, info)
            }
            vir_low::Expression::InhaleExhale(expression) => {
                expression.expression_to_smt2(writer, info)
            }
        }
    }
}

impl<'a, 'c, EC: EncoderContext> Expr2Smt<Info<'a, 'c, EC>>
    for Expr2SmtWrapper<'a, vir_low::VariableDecl>
{
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: Info<'a, 'c, EC>) -> SmtRes<()>
    where
        Writer: Write,
    {
        write!(writer, "(")?;
        write!(writer, "{}", self.expr.name)?;
        write!(writer, " ")?;
        self.expr.ty.type_to_smt2(writer)?;
        write!(writer, ")")?;
        Ok(())
    }
}

impl<'a, 'c, EC: EncoderContext> Expr2Smt<Info<'a, 'c, EC>>
    for Expr2SmtWrapper<'a, vir_low::Local>
{
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: Info<'a, 'c, EC>) -> SmtRes<()>
    where
        Writer: Write,
    {
        write!(writer, "{}", self.expr.variable.name)?;
        Ok(())
    }
}

impl<'a, 'c, EC: EncoderContext> Expr2Smt<Info<'a, 'c, EC>>
    for Expr2SmtWrapper<'a, vir_low::Field>
{
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: Info<'a, 'c, EC>) -> SmtRes<()>
    where
        Writer: Write,
    {
        unimplemented!()
    }
}

impl<'a, 'c, EC: EncoderContext> Expr2Smt<Info<'a, 'c, EC>>
    for Expr2SmtWrapper<'a, vir_low::LabelledOld>
{
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: Info<'a, 'c, EC>) -> SmtRes<()>
    where
        Writer: Write,
    {
        unreachable!("Should be desugared by the caller: {}", self.expr);
    }
}

impl<'a, 'c, EC: EncoderContext> Expr2Smt<Info<'a, 'c, EC>>
    for Expr2SmtWrapper<'a, vir_low::Constant>
{
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: Info<'a, 'c, EC>) -> SmtRes<()>
    where
        Writer: Write,
    {
        match &self.expr.value {
            vir_low::ConstantValue::Bool(true) => write!(writer, "true")?,
            vir_low::ConstantValue::Bool(false) => write!(writer, "false")?,
            vir_low::ConstantValue::Int(value) => write!(writer, "{}", value)?,
            vir_low::ConstantValue::BigInt(value) => write!(writer, "{}", value)?,
        }
        Ok(())
    }
}

impl<'a, 'c, EC: EncoderContext> Expr2Smt<Info<'a, 'c, EC>>
    for Expr2SmtWrapper<'a, vir_low::MagicWand>
{
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: Info<'a, 'c, EC>) -> SmtRes<()>
    where
        Writer: Write,
    {
        unimplemented!()
    }
}

impl<'a, 'c, EC: EncoderContext> Expr2Smt<Info<'a, 'c, EC>>
    for Expr2SmtWrapper<'a, vir_low::PredicateAccessPredicate>
{
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: Info<'a, 'c, EC>) -> SmtRes<()>
    where
        Writer: Write,
    {
        unimplemented!()
    }
}

impl<'a, 'c, EC: EncoderContext> Expr2Smt<Info<'a, 'c, EC>>
    for Expr2SmtWrapper<'a, vir_low::FieldAccessPredicate>
{
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: Info<'a, 'c, EC>) -> SmtRes<()>
    where
        Writer: Write,
    {
        unimplemented!()
    }
}

impl<'a, 'c, EC: EncoderContext> Expr2Smt<Info<'a, 'c, EC>>
    for Expr2SmtWrapper<'a, vir_low::Unfolding>
{
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: Info<'a, 'c, EC>) -> SmtRes<()>
    where
        Writer: Write,
    {
        unimplemented!()
    }
}

impl<'a, 'c, EC: EncoderContext> Expr2Smt<Info<'a, 'c, EC>>
    for Expr2SmtWrapper<'a, vir_low::UnaryOp>
{
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: Info<'a, 'c, EC>) -> SmtRes<()>
    where
        Writer: Write,
    {
        match self.expr.op_kind {
            vir_low::UnaryOpKind::Not => {
                write!(writer, "(not ")?;
            }
            vir_low::UnaryOpKind::Minus => {
                write!(writer, "(- ")?;
            }
        }
        self.expr.argument.expression_to_smt2(writer, info)?;
        write!(writer, " )")?;
        Ok(())
    }
}

impl<'a, 'c, EC: EncoderContext> Expr2Smt<Info<'a, 'c, EC>>
    for Expr2SmtWrapper<'a, vir_low::BinaryOp>
{
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: Info<'a, 'c, EC>) -> SmtRes<()>
    where
        Writer: Write,
    {
        write!(writer, "(")?;
        match self.expr.op_kind {
            vir_low::BinaryOpKind::EqCmp => write!(writer, "=")?,
            vir_low::BinaryOpKind::NeCmp => {
                write!(writer, "not (= ")?;
            }
            vir_low::BinaryOpKind::GtCmp => write!(writer, ">")?,
            vir_low::BinaryOpKind::GeCmp => write!(writer, ">=")?,
            vir_low::BinaryOpKind::LtCmp => write!(writer, "<")?,
            vir_low::BinaryOpKind::LeCmp => write!(writer, "<=")?,
            vir_low::BinaryOpKind::Add => write!(writer, "+")?,
            vir_low::BinaryOpKind::Sub => write!(writer, "-")?,
            vir_low::BinaryOpKind::Mul => write!(writer, "*")?,
            vir_low::BinaryOpKind::Div => {
                if matches!(self.expr.left.get_type(), vir_low::Type::Int) {
                    write!(writer, "div")?
                } else {
                    write!(writer, "/")?
                }
            }
            vir_low::BinaryOpKind::Mod => write!(writer, "mod")?,
            vir_low::BinaryOpKind::And => write!(writer, "and")?,
            vir_low::BinaryOpKind::Or => write!(writer, "or")?,
            vir_low::BinaryOpKind::Implies => write!(writer, "=>")?,
        }
        write!(writer, " ")?;
        self.expr.left.expression_to_smt2(writer, info)?;
        write!(writer, " ")?;
        self.expr.right.expression_to_smt2(writer, info)?;
        write!(writer, " )")?;
        if self.expr.op_kind == vir_low::BinaryOpKind::NeCmp {
            write!(writer, " )")?;
        }
        Ok(())
    }
}

impl<'a, 'c, EC: EncoderContext> Expr2Smt<Info<'a, 'c, EC>>
    for Expr2SmtWrapper<'a, vir_low::PermBinaryOp>
{
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: Info<'a, 'c, EC>) -> SmtRes<()>
    where
        Writer: Write,
    {
        write!(writer, "(")?;
        match self.expr.op_kind {
            vir_low::PermBinaryOpKind::Add => write!(writer, "+")?,
            vir_low::PermBinaryOpKind::Sub => write!(writer, "-")?,
            vir_low::PermBinaryOpKind::Mul => write!(writer, "*")?,
            vir_low::PermBinaryOpKind::Div => write!(writer, "/")?,
        }
        write!(writer, " ")?;
        self.expr.left.expression_to_smt2(writer, info)?;
        write!(writer, " ")?;
        self.expr.right.expression_to_smt2(writer, info)?;
        write!(writer, " )")?;
        Ok(())
    }
}

impl<'a, 'c, EC: EncoderContext> Expr2Smt<Info<'a, 'c, EC>>
    for Expr2SmtWrapper<'a, vir_low::ContainerOp>
{
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: Info<'a, 'c, EC>) -> SmtRes<()>
    where
        Writer: Write,
    {
        unreachable!(
            "ContainerOp should be desugared before this point: {}",
            self.expr
        );
        // write!(writer, "(")?;
        // self.expr.container_type.type_to_smt2(writer, info)?;
        // write!(writer, "@{}", self.expr.kind)?;
        // for arg in &self.expr.operands {
        //     write!(writer, " ")?;
        //     arg.expression_to_smt2(writer, info)?;
        // }
        // write!(writer, ")")?;
        // Ok(())
    }
}

impl<'a, 'c, EC: EncoderContext> Expr2Smt<Info<'a, 'c, EC>>
    for Expr2SmtWrapper<'a, vir_low::ConditionalExpression>
{
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: Info<'a, 'c, EC>) -> SmtRes<()>
    where
        Writer: Write,
    {
        unimplemented!()
    }
}

impl<'a, 'c, EC: EncoderContext> Expr2Smt<Info<'a, 'c, EC>>
    for Expr2SmtWrapper<'a, vir_low::Quantifier>
{
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: Info<'a, 'c, EC>) -> SmtRes<()>
    where
        Writer: Write,
    {
        let expr = self.expr;
        match expr.kind {
            vir_low::QuantifierKind::ForAll => write!(writer, "(forall (")?,
            vir_low::QuantifierKind::Exists => write!(writer, "(exists (")?,
        }
        for variable in &expr.variables {
            variable.expression_to_smt2(writer, info)?;
        }
        write!(writer, ") (! ")?;
        Expr2SmtWrapper::new(&*expr.body).expr_to_smt2(writer, info)?;
        for trigger in &expr.triggers {
            trigger.expression_to_smt2(writer, info)?;
        }
        write!(writer, " ))")?;
        Ok(())
    }
}

impl<'a, 'c, EC: EncoderContext> Expr2Smt<Info<'a, 'c, EC>>
    for Expr2SmtWrapper<'a, vir_low::Trigger>
{
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: Info<'a, 'c, EC>) -> SmtRes<()>
    where
        Writer: Write,
    {
        write!(writer, " :pattern (")?;
        for part in &self.expr.terms {
            part.expression_to_smt2(writer, info)?;
        }
        write!(writer, ")")?;
        Ok(())
    }
}

impl<'a, 'c, EC: EncoderContext> Expr2Smt<Info<'a, 'c, EC>>
    for Expr2SmtWrapper<'a, vir_low::LetExpr>
{
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: Info<'a, 'c, EC>) -> SmtRes<()>
    where
        Writer: Write,
    {
        unimplemented!()
    }
}

impl<'a, 'c, EC: EncoderContext> Expr2Smt<Info<'a, 'c, EC>>
    for Expr2SmtWrapper<'a, vir_low::FuncApp>
{
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: Info<'a, 'c, EC>) -> SmtRes<()>
    where
        Writer: Write,
    {
        unreachable!("FuncApp: {}. Should be desugared by the caller.", self.expr);
    }
}

impl<'a, 'c, EC: EncoderContext> Expr2Smt<Info<'a, 'c, EC>>
    for Expr2SmtWrapper<'a, vir_low::DomainFuncApp>
{
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: Info<'a, 'c, EC>) -> SmtRes<()>
    where
        Writer: Write,
    {
        if self.expr.arguments.is_empty() {
            write!(
                writer,
                "{}@{}",
                self.expr.domain_name, self.expr.function_name
            )?;
        } else {
            write!(writer, "(")?;
            write!(
                writer,
                "{}@{}",
                self.expr.domain_name, self.expr.function_name
            )?;
            for arg in &self.expr.arguments {
                write!(writer, " ")?;
                arg.expression_to_smt2(writer, info)?;
            }
            write!(writer, ")")?;
        }
        Ok(())
    }
}

impl<'a, 'c, EC: EncoderContext> Expr2Smt<Info<'a, 'c, EC>>
    for Expr2SmtWrapper<'a, vir_low::InhaleExhale>
{
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: Info<'a, 'c, EC>) -> SmtRes<()>
    where
        Writer: Write,
    {
        unimplemented!()
    }
}
