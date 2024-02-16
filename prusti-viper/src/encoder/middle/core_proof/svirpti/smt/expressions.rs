use rsmt2::{print::Expr2Smt, SmtRes};
use std::io::Write;
use vir_crate::low::{self as vir_low};

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

impl<'a> Expr2Smt for Expr2SmtWrapper<'a, vir_low::Expression> {
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: ()) -> SmtRes<()>
    where
        Writer: Write,
    {
        match self.expr {
            vir_low::Expression::Local(expression) => Expr2SmtWrapper::new(expression).expr_to_smt2(writer, info),
            vir_low::Expression::Field(expression) => Expr2SmtWrapper::new(expression).expr_to_smt2(writer, info),
            vir_low::Expression::LabelledOld(expression) => Expr2SmtWrapper::new(expression).expr_to_smt2(writer, info),
            vir_low::Expression::Constant(expression) => Expr2SmtWrapper::new(expression).expr_to_smt2(writer, info),
            vir_low::Expression::MagicWand(expression) => Expr2SmtWrapper::new(expression).expr_to_smt2(writer, info),
            vir_low::Expression::PredicateAccessPredicate(expression) => Expr2SmtWrapper::new(expression).expr_to_smt2(writer, info),
            vir_low::Expression::FieldAccessPredicate(expression) => Expr2SmtWrapper::new(expression).expr_to_smt2(writer, info),
            vir_low::Expression::Unfolding(expression) => Expr2SmtWrapper::new(expression).expr_to_smt2(writer, info),
            vir_low::Expression::UnaryOp(expression) => Expr2SmtWrapper::new(expression).expr_to_smt2(writer, info),
            vir_low::Expression::BinaryOp(expression) => Expr2SmtWrapper::new(expression).expr_to_smt2(writer, info),
            vir_low::Expression::PermBinaryOp(expression) => Expr2SmtWrapper::new(expression).expr_to_smt2(writer, info),
            vir_low::Expression::ContainerOp(expression) => Expr2SmtWrapper::new(expression).expr_to_smt2(writer, info),
            vir_low::Expression::Conditional(expression) => Expr2SmtWrapper::new(expression).expr_to_smt2(writer, info),
            vir_low::Expression::Quantifier(expression) => Expr2SmtWrapper::new(expression).expr_to_smt2(writer, info),
            vir_low::Expression::LetExpr(expression) => Expr2SmtWrapper::new(expression).expr_to_smt2(writer, info),
            vir_low::Expression::FuncApp(expression) => Expr2SmtWrapper::new(expression).expr_to_smt2(writer, info),
            vir_low::Expression::DomainFuncApp(expression) => Expr2SmtWrapper::new(expression).expr_to_smt2(writer, info),
            vir_low::Expression::InhaleExhale(expression) => Expr2SmtWrapper::new(expression).expr_to_smt2(writer, info),
        }
    }
}

impl<'a> Expr2Smt for Expr2SmtWrapper<'a, vir_low::VariableDecl> {
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: ()) -> SmtRes<()>
    where
        Writer: Write,
    {
        unimplemented!()
    }
}

impl<'a> Expr2Smt for Expr2SmtWrapper<'a, vir_low::Local> {
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: ()) -> SmtRes<()>
    where
        Writer: Write,
    {
        unimplemented!()
    }
}

impl<'a> Expr2Smt for Expr2SmtWrapper<'a, vir_low::Field> {
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: ()) -> SmtRes<()>
    where
        Writer: Write,
    {
        unimplemented!()
    }
}

impl<'a> Expr2Smt for Expr2SmtWrapper<'a, vir_low::LabelledOld> {
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: ()) -> SmtRes<()>
    where
        Writer: Write,
    {
        unimplemented!()
    }
}

impl<'a> Expr2Smt for Expr2SmtWrapper<'a, vir_low::Constant> {
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: ()) -> SmtRes<()>
    where
        Writer: Write,
    {
        unimplemented!()
    }
}

impl<'a> Expr2Smt for Expr2SmtWrapper<'a, vir_low::MagicWand> {
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: ()) -> SmtRes<()>
    where
        Writer: Write,
    {
        unimplemented!()
    }
}

impl<'a> Expr2Smt for Expr2SmtWrapper<'a, vir_low::PredicateAccessPredicate> {
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: ()) -> SmtRes<()>
    where
        Writer: Write,
    {
        unimplemented!()
    }
}

impl<'a> Expr2Smt for Expr2SmtWrapper<'a, vir_low::FieldAccessPredicate> {
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: ()) -> SmtRes<()>
    where
        Writer: Write,
    {
        unimplemented!()
    }
}

impl<'a> Expr2Smt for Expr2SmtWrapper<'a, vir_low::Unfolding> {
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: ()) -> SmtRes<()>
    where
        Writer: Write,
    {
        unimplemented!()
    }
}

impl<'a> Expr2Smt for Expr2SmtWrapper<'a, vir_low::UnaryOp> {
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: ()) -> SmtRes<()>
    where
        Writer: Write,
    {
        unimplemented!()
    }
}

impl<'a> Expr2Smt for Expr2SmtWrapper<'a, vir_low::BinaryOp> {
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: ()) -> SmtRes<()>
    where
        Writer: Write,
    {
        unimplemented!()
    }
}

impl<'a> Expr2Smt for Expr2SmtWrapper<'a, vir_low::PermBinaryOp> {
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: ()) -> SmtRes<()>
    where
        Writer: Write,
    {
        unimplemented!()
    }
}

impl<'a> Expr2Smt for Expr2SmtWrapper<'a, vir_low::ContainerOp> {
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: ()) -> SmtRes<()>
    where
        Writer: Write,
    {
        unimplemented!()
    }
}

impl<'a> Expr2Smt for Expr2SmtWrapper<'a, vir_low::ConditionalExpression> {
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: ()) -> SmtRes<()>
    where
        Writer: Write,
    {
        unimplemented!()
    }
}

impl<'a> Expr2Smt for Expr2SmtWrapper<'a, vir_low::Quantifier> {
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: ()) -> SmtRes<()>
    where
        Writer: Write,
    {
        let expr = self.expr;
        match expr.kind {
            vir_low::QuantifierKind::ForAll => write!(writer, "(forall (")?,
            vir_low::QuantifierKind::Exists => write!(writer, "(exists (")?,
        }
        for variable in &expr.variables {
            Expr2SmtWrapper::new(variable).expr_to_smt2(writer, info)?;
        }
        write!(writer, ") (! ")?;
        Expr2SmtWrapper::new(&*expr.body).expr_to_smt2(writer, info)?;
        for trigger in &expr.triggers {
            Expr2SmtWrapper::new(trigger).expr_to_smt2(writer, info)?;
        }
        write!(writer, " ))")?;
        Ok(())
    }
}

impl<'a> Expr2Smt for Expr2SmtWrapper<'a, vir_low::Trigger> {
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: ()) -> SmtRes<()>
    where
        Writer: Write,
    {
        unimplemented!()
    }
}

impl<'a> Expr2Smt for Expr2SmtWrapper<'a, vir_low::LetExpr> {
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: ()) -> SmtRes<()>
    where
        Writer: Write,
    {
        unimplemented!()
    }
}

impl<'a> Expr2Smt for Expr2SmtWrapper<'a, vir_low::FuncApp> {
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: ()) -> SmtRes<()>
    where
        Writer: Write,
    {
        unimplemented!()
    }
}

impl<'a> Expr2Smt for Expr2SmtWrapper<'a, vir_low::DomainFuncApp> {
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: ()) -> SmtRes<()>
    where
        Writer: Write,
    {
        unimplemented!()
    }
}

impl<'a> Expr2Smt for Expr2SmtWrapper<'a, vir_low::InhaleExhale> {
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: ()) -> SmtRes<()>
    where
        Writer: Write,
    {
        unimplemented!()
    }
}