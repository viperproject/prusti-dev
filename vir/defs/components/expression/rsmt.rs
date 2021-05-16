trait Interface {
    type UninterpretedSortSymbol;
    type Context;
}

use super::*;

vir_raw_block! { Variable =>
    impl<'a, C: Context> ::rsmt2::print::Expr2Smt<&'a C> for Variable {
        fn expr_to_smt2<Writer: std::io::Write>(
            &self,
            writer: &mut Writer,
            context: &'a C
        ) -> ::rsmt2::SmtRes<()> {
            context.write_variable_symbol(writer, &self.name)?;
            Ok(())
        }
    }
}
vir_raw_block! { Constant =>
    impl<'a, C: Context> ::rsmt2::print::Expr2Smt<&'a C> for Constant {
        fn expr_to_smt2<Writer: std::io::Write>(
            &self,
            writer: &mut Writer,
            _context: &'a C
        ) -> ::rsmt2::SmtRes<()> {
            match self {
                Constant::Bool(true) => write!(writer, "true")?,
                Constant::Bool(false) => write!(writer, "true")?,
                Constant::Int(value) => write!(writer, "{}", value)?,
            }
            Ok(())
        }
    }
}
vir_raw_block! { UnaryOperation =>
    impl<'a, C: Context> ::rsmt2::print::Expr2Smt<&'a C> for UnaryOperation {
        fn expr_to_smt2<Writer: std::io::Write>(
            &self,
            writer: &mut Writer,
            context: &'a C
        ) -> ::rsmt2::SmtRes<()> {
            match self.kind {
                UnaryOperationKind::Not => {
                    write!(writer, "(not ")?;
                }
                UnaryOperationKind::Minus => {
                    write!(writer, "(- ")?;
                }
            }
            self.arg.expr_to_smt2(writer, context)?;
            write!(writer, " )")?;
            Ok(())
        }
    }
}
vir_raw_block! { BinaryOperation =>
    impl<'a, C: Context> ::rsmt2::print::Expr2Smt<&'a C> for BinaryOperation {
        fn expr_to_smt2<Writer: std::io::Write>(
            &self,
            writer: &mut Writer,
            context: &'a C
        ) -> ::rsmt2::SmtRes<()> {
            write!(writer, "(")?;
            match self.kind {
                BinaryOperationKind::EqCmp => write!(writer, "=")?,
                BinaryOperationKind::NeCmp => {
                    write!(writer, "not (= ")?;
                }
                BinaryOperationKind::GtCmp => write!(writer, ">")?,
                BinaryOperationKind::GeCmp => write!(writer, ">=")?,
                BinaryOperationKind::LtCmp => write!(writer, "<")?,
                BinaryOperationKind::LeCmp => write!(writer, "<=")?,
                BinaryOperationKind::Add => write!(writer, "+")?,
                BinaryOperationKind::Sub => write!(writer, "-")?,
                BinaryOperationKind::Mul => write!(writer, "*")?,
                BinaryOperationKind::Div => {
                    if self.left.sort(context).is_integer() {
                        write!(writer, "div")?
                    } else {
                        write!(writer, "/")?
                    }
                }
                BinaryOperationKind::Mod => write!(writer, "mod")?,
                BinaryOperationKind::And => write!(writer, "and")?,
                BinaryOperationKind::Or => write!(writer, "or")?,
                BinaryOperationKind::Implies => write!(writer, "=>")?,
            }
            write!(writer, " ")?;
            self.left.expr_to_smt2(writer, context)?;
            write!(writer, " ")?;
            self.right.expr_to_smt2(writer, context)?;
            write!(writer, " )")?;
            if self.kind == BinaryOperationKind::NeCmp {
                write!(writer, " )")?;
            }
            Ok(())
        }
    }
}
vir_raw_block! { Conditional =>
    impl<'a, C: Context> ::rsmt2::print::Expr2Smt<&'a C> for Conditional {
        fn expr_to_smt2<Writer: std::io::Write>(
            &self,
            writer: &mut Writer,
            context: &'a C
        ) -> ::rsmt2::SmtRes<()> {
            write!(writer, "(ite ")?;
            self.guard.expr_to_smt2(writer, context)?;
            write!(writer, " ")?;
            self.then_expr.expr_to_smt2(writer, context)?;
            write!(writer, " ")?;
            self.else_expr.expr_to_smt2(writer, context)?;
            write!(writer, ")")?;
            Ok(())
        }
    }
}
vir_raw_block! { Quantifier =>
    impl<'a, C: Context> ::rsmt2::print::Expr2Smt<&'a C> for Quantifier {
        fn expr_to_smt2<Writer: std::io::Write>(
            &self,
            writer: &mut Writer,
            context: &'a C
        ) -> ::rsmt2::SmtRes<()> {
            match self.kind {
                QuantifierKind::ForAll => write!(writer, "(forall (")?,
                QuantifierKind::Exists => write!(writer, "(exists (")?,
            }
            for BoundedVariableDecl { name, sort } in &self.variables {
                write!(writer, "(")?;
                context.write_variable_symbol(writer, name)?;
                write!(writer, " ")?;
                ::rsmt2::print::Sort2Smt::sort_to_smt2(&sort, writer, context)?;
                write!(writer, ")")?;
            }
            write!(writer, ") (! ")?;
            self.body.expr_to_smt2(writer, context)?;
            for trigger in &self.triggers {
                trigger.expr_to_smt2(writer, context)?;
            }
            write!(writer, " ))")?;
            Ok(())
        }
    }
}
vir_raw_block! { Trigger =>
    impl<'a, C: Context> ::rsmt2::print::Expr2Smt<&'a C> for Trigger {
        fn expr_to_smt2<Writer: std::io::Write>(
            &self,
            writer: &mut Writer,
            context: &'a C
        ) -> ::rsmt2::SmtRes<()> {
            write!(writer, " :pattern (")?;
            for part in &self.parts {
                part.expr_to_smt2(writer, context)?;
            }
            write!(writer, ")")?;
            Ok(())
        }
    }
}
vir_raw_block! { FunctionApplication =>
    impl<'a, C: Context> ::rsmt2::print::Expr2Smt<&'a C> for FunctionApplication {
        fn expr_to_smt2<Writer: std::io::Write>(
            &self,
            writer: &mut Writer,
            context: &'a C
        ) -> ::rsmt2::SmtRes<()> {
            if self.args.is_empty() {
                self.function.expr_to_smt2(writer, context)?;
            } else {
                write!(writer, "(")?;
                self.function.expr_to_smt2(writer, context)?;
                for arg in &self.args {
                    write!(writer, " ")?;
                    arg.expr_to_smt2(writer, context)?;
                }
                write!(writer, ")")?;
            }
            Ok(())
        }
    }
}
vir_raw_block! { LabelledExpression =>
    impl<'a, C: Context> ::rsmt2::print::Expr2Smt<&'a C> for LabelledExpression {
        fn expr_to_smt2<Writer: std::io::Write>(
            &self,
            writer: &mut Writer,
            context: &'a C
        ) -> ::rsmt2::SmtRes<()> {
            match self.positivity {
                LabelPositivity::Positive => {
                    write!(writer,
                        "(! (and ",
                    )?;
                    context.write_label_symbol(writer, &self.name)?;
                    write!(writer, " ")?;
                    self.expression.expr_to_smt2(writer, context)?;
                    write!(
                        writer,
                        ") :lblpos ",
                    )?;
                    context.write_label_symbol(writer, &self.name)?;
                    write!(writer, ")")?;
                }
                LabelPositivity::Negative => {
                    write!(
                        writer,
                        "(! (or ",
                    )?;
                    context.write_label_symbol(writer, &self.name)?;
                    write!(writer, " ")?;
                    self.expression.expr_to_smt2(writer, context)?;
                    write!(
                        writer,
                        ") :lblneg ",
                    )?;
                    context.write_label_symbol(writer, &self.name)?;
                    write!(writer, ")")?;
                }
            }
            Ok(())
        }
    }
}
