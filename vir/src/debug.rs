use std::fmt::{Debug, Display, Formatter, Result as FmtResult};

use crate::data::*;
use crate::gendata::*;

fn fmt_comma_sep_display<T: Display>(f: &mut Formatter<'_>, els: &[T]) -> FmtResult {
    els.iter()
        .enumerate()
        .map(|(idx, el)| {
            if idx > 0 { write!(f, ", ")? }
            el.fmt(f)
        })
        .collect::<FmtResult>()
}
fn fmt_comma_sep<T: Debug>(f: &mut Formatter<'_>, els: &[T]) -> FmtResult {
    els.iter()
        .enumerate()
        .map(|(idx, el)| {
            if idx > 0 { write!(f, ", ")? }
            el.fmt(f)
        })
        .collect::<FmtResult>()
}
fn fmt_comma_sep_lines<T: Debug>(f: &mut Formatter<'_>, els: &[T]) -> FmtResult {
    for (idx, el) in els.iter().enumerate() {
        write!(f, "  {:?}", el)?;
        if idx < els.len() - 1 {
            write!(f, ",")?;
        }
        writeln!(f, "")?;
    }
    Ok(())
}
fn indent(s: String) -> String {
    s
        .split("\n")
        .intersperse("\n  ")
        .collect::<String>()
}

impl<'vir, Curr, Next> Debug for AccFieldGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "acc({:?}.{}", self.recv, self.field.name)?;
        if let Some(perm) = self.perm {
            write!(f, ", {perm:?}")?;
        }
        write!(f, ")")
    }
}

impl<'vir, Curr, Next> Debug for BinOpGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "(")?;
        self.lhs.fmt(f)?;
        write!(f, ") {} (", match self.kind {
            BinOpKind::CmpEq => "==",
            BinOpKind::CmpNe => "!=",
            BinOpKind::CmpGt => ">",
            BinOpKind::CmpGe => ">=",
            BinOpKind::CmpLt => "<",
            BinOpKind::CmpLe => "<=",
            BinOpKind::And => "&&",
            BinOpKind::Or => "||",
            BinOpKind::Add => "+",
            BinOpKind::Sub => "-",
            BinOpKind::Mod => "%",
        })?;
        self.rhs.fmt(f)?;
        write!(f, ")")
    }
}

impl Debug for CfgBlockLabelData {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self::Start => write!(f, "start"),
            Self::End => write!(f, "end"),
            Self::BasicBlock(idx) => write!(f, "bb_{}", idx),
        }
    }
}

impl Debug for ConstData {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self::Bool(b) => write!(f, "{b}"),
            Self::Int(n) => write!(f, "{n}"),
            Self::Wildcard => write!(f, "wildcard"),
            Self::Null => write!(f, "null"),
        }
    }
}

impl<'vir, Curr, Next> Debug for DomainGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "domain {}", self.name)?;
        if !self.typarams.is_empty() {
            write!(f, "[")?;
            fmt_comma_sep_display(f, &self.typarams)?;
            write!(f, "]")?;
        }
        writeln!(f, " {{")?;
        self.axioms.iter().map(|el| el.fmt(f)).collect::<FmtResult>()?;
        self.functions.iter().map(|el| el.fmt(f)).collect::<FmtResult>()?;
        writeln!(f, "}}")
    }
}

impl<'vir, Curr, Next> Debug for DomainAxiomGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        writeln!(f, "  axiom {} {{", self.name)?;
        writeln!(f, "    {:?}", self.expr)?;
        writeln!(f, "  }}")
    }
}

impl<'vir> Debug for DomainFunctionData<'vir> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "  ")?;
        if self.unique {
            write!(f, "unique ")?;
        }
        write!(f, "function {}(", self.name)?;
        fmt_comma_sep(f, &self.args)?;
        writeln!(f, "): {:?}", self.ret)
    }
}

impl<'vir, Curr, Next> Debug for ExprGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        // TODO: Position, etc
        self.kind.fmt(f)
    }
}

impl<'vir, Curr, Next> Debug for ExprKindGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self::AccField(e) => e.fmt(f),
            Self::BinOp(e) => e.fmt(f),
            Self::Const(e) => e.fmt(f),
            Self::Result => write!(f, "result"),
            Self::Field(e, field) => write!(f, "{:?}.{}", e, field.name),
            Self::Forall(e) => e.fmt(f),
            Self::FuncApp(e) => e.fmt(f),
            Self::Let(e) => e.fmt(f),
            Self::Lazy(desc, _) => write!(f, "%%/*{desc}*/"),
            Self::Local(e) => e.fmt(f),
            Self::Old(e) => write!(f, "old({:?})", e),
            Self::PredicateApp(e) => e.fmt(f),
            Self::Ternary(e) => e.fmt(f),
            Self::UnOp(e) => e.fmt(f),
            Self::Unfolding(e) => e.fmt(f),
            Self::Todo(e) => write!(f, "{}", e),
        }
    }
}

impl<'vir> Debug for FieldData<'vir> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        writeln!(f, "field {}: {:?}", self.name, self.ty)
    }
}

impl<'vir, Curr, Next> Debug for ForallGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "forall ")?;
        fmt_comma_sep(f, &self.qvars)?;
        write!(f, " ::")?;
        for trigger in self.triggers {
            write!(f, " {{")?;
            fmt_comma_sep(f, trigger)?;
            write!(f, "}}")?;
        }
        write!(f, " {:?}", self.body)
    }
}

impl<'vir, Curr, Next> Debug for FuncAppGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        if self.result_ty.is_some() {
            write!(f, "(")?;
        }
        write!(f, "{}(", self.target)?;
        fmt_comma_sep(f, &self.args)?;
        write!(f, ")")?;
        if let Some(rt) = self.result_ty {
            write!(f, ": {rt:?})")?;
        }
        Ok(())
    }
}

impl<'vir, Curr, Next> Debug for FunctionGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        writeln!(f, "function {}(", self.name)?;
        fmt_comma_sep_lines(f, &self.args)?;
        writeln!(f, "): {:?}", self.ret)?;
        self.pres.iter().map(|el| writeln!(f, "  requires {:?}", el)).collect::<FmtResult>()?;
        self.posts.iter().map(|el| writeln!(f, "  ensures {:?}", el)).collect::<FmtResult>()?;
        if let Some(expr) = self.expr {
            write!(f, "{{\n  ")?;
            expr.fmt(f)?;
            writeln!(f, "\n}}")?;
        }
        Ok(())
    }
}

impl<'vir, Curr, Next> Debug for LetGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        // write!(f, "(let {} == ({:?}) in {:?})", self.name, self.val, self.expr)

        // slightly nicer spacing for debugging:
        // - indent lines within `val`
        // - start the `expr` on a new line
        let str_val = indent(format!("{:?}", self.val));
        write!(f, "(let {} == ({str_val}) in\n{:?})", self.name, self.expr)
    }
}

impl<'vir> Debug for LocalData<'vir> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", self.name)
    }
}

impl<'vir> Debug for LocalDeclData<'vir> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}: ", self.name)?;
        self.ty.fmt(f)?;
        Ok(())
    }
}

impl<'vir, Curr, Next> Debug for MethodGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        writeln!(f, "method {}(", self.name)?;
        fmt_comma_sep_lines(f, &self.args)?;
        if !self.rets.is_empty() {
            writeln!(f, ") returns (")?;
            fmt_comma_sep_lines(f, &self.rets)?;
            writeln!(f, ")")?;
        } else {
            writeln!(f, ")")?;
        }
        self.pres.iter().map(|el| writeln!(f, "  requires {:?}", el)).collect::<FmtResult>()?;
        self.posts.iter().map(|el| writeln!(f, "  ensures {:?}", el)).collect::<FmtResult>()?;
        if let Some(blocks) = self.blocks.as_ref() {
            writeln!(f, "{{")?;
            for block in blocks.iter() {
                writeln!(f, "label {:?}", block.label)?;
                for stmt in block.stmts {
                    writeln!(f, "  {:?}", stmt)?;
                }
                writeln!(f, "  {:?}", block.terminator)?;
            }
            writeln!(f, "}}")?;
        }
        Ok(())
    }
}

impl<'vir, Curr, Next> Debug for PredicateGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "predicate {}(", self.name)?;
        fmt_comma_sep(f, &self.args)?;
        write!(f, ")")?;
        if let Some(expr) = self.expr {
            write!(f, " {{\n  ")?;
            expr.fmt(f)?;
            writeln!(f, "\n}}")
        } else {
            writeln!(f, "")
        }
    }
}

impl<'vir, Curr, Next> Debug for PredicateAppGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        if self.perm.is_some() {
            write!(f, "acc(")?;
        }
        write!(f, "{}(", self.target)?;
        fmt_comma_sep(f, &self.args)?;
        write!(f, ")")?;
        if let Some(perm) = self.perm {
            write!(f, ", {perm:?})")?;
        }
        Ok(())
    }
}

impl<'vir, Curr, Next> Debug for StmtGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self::LocalDecl(decl, expr) => {
                write!(f, "var {:?}", decl)?;
                if let Some(expr) = expr {
                    write!(f, " := {:?}", expr)?;
                }
                Ok(())
            }
            Self::PureAssign(data) => write!(f, "{:?} := {:?}", data.lhs, data.rhs),
            Self::Inhale(data) => write!(f, "inhale {:?}", data),
            Self::Exhale(data) => write!(f, "exhale {:?}", data),
            Self::Unfold(data) => write!(f, "unfold {:?}", data),
            Self::Fold(data) => write!(f, "fold {:?}", data),
            Self::MethodCall(data) => {
                if !data.targets.is_empty() {
                    fmt_comma_sep(f, &data.targets)?;
                    write!(f, " := ")?;
                }
                write!(f, "{}(", data.method)?;
                fmt_comma_sep(f, &data.args)?;
                write!(f, ")")
            }
            Self::Comment(info) => write!(f, "// {}", info),
            Self::Dummy(info) => write!(f, "// {}", info),
        }
    }
}

impl<'vir, Curr, Next> Debug for TerminatorStmtGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self::AssumeFalse => write!(f, "assume false"),
            Self::Goto(target) => write!(f, "goto {:?}", target),
            Self::GotoIf(data) => {
                if data.targets.is_empty() {
                    write!(f, "goto {:?}", data.otherwise)
                } else {
                    for target in data.targets {
                        write!(f, "if ({:?} == {:?}) {{", data.value, target.0)?;
                        for extra in target.2 {
                            write!(f, "{extra:?}")?;
                        }
                        write!(f, " goto {:?} }}\n  else", target.1)?;
                    }
                    write!(f, " {{ ")?;
                    for extra in data.otherwise_statements {
                        write!(f, "{extra:?}")?;
                    }
                    write!(f, "goto {:?} }}", data.otherwise)
                }
            }
            Self::Exit => write!(f, "// return"),
            Self::Dummy(info) => write!(f, "assert false // {}", info),
        }
    }
}

impl<'vir, Curr, Next> Debug for TernaryGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        //write!(f, "{:?} ? {:?} : {:?}", self.cond, self.then, self.else_)

        // slightly nicer spacing for debugging:
        // - split off each case to new, indented line
        let str_then = indent(format!("{:?}", self.then));
        let str_else = indent(format!("{:?}", self.else_));
        write!(f, "{:?}\n? {str_then}\n: {str_else}", self.cond)
    }
}

impl<'vir> Debug for TypeData<'vir> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self::Int { .. } => write!(f, "Int"),
            Self::Bool => write!(f, "Bool"),
            Self::DomainTypeParam(name) => write!(f, "{name}"),
            Self::Domain(name, params) => {
                write!(f, "{name}")?;
                if !params.is_empty() {
                    write!(f, "[")?;
                    fmt_comma_sep(f, &params)?;
                    write!(f, "]")?;
                }
                Ok(())
            }
            Self::Ref => write!(f, "Ref"),
            Self::Perm => write!(f, "Perm"),
            Self::Unsupported(u) => u.fmt(f)
        }
    }
}

impl<'vir> Debug for UnsupportedType<'vir> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "UnsupportedType({})", self.name)
    }
}

impl<'vir> Display for DomainParamData<'vir> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", self.name)
    }
}

impl<'vir, Curr, Next> Debug for UnOpGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}({:?})", match self.kind {
            UnOpKind::Neg => "-",
            UnOpKind::Not => "!",
        }, self.expr)
    }
}

impl<'vir, Curr, Next> Debug for UnfoldingGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "unfolding {:?} in ({:?})", self.target, self.expr)
    }
}
