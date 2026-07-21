use std::fmt::{Debug, Display, Formatter, Result as FmtResult};

use crate::{data::*, gendata::*, CompType};

fn fmt_comma_sep_display<T: Display>(f: &mut Formatter<'_>, els: &[T]) -> FmtResult {
    els.iter().enumerate().try_for_each(|(idx, el)| {
        if idx > 0 {
            write!(f, ", ")?
        }
        el.fmt(f)
    })
}
fn fmt_comma_sep<T: Debug>(f: &mut Formatter<'_>, els: &[T]) -> FmtResult {
    let indent = f.width().unwrap_or_default();
    els.iter().enumerate().try_for_each(|(idx, el)| {
        if idx > 0 {
            write!(f, ", ")?
        }
        write!(f, "{el:indent$?}")
    })
}
fn fmt_comma_sep_lines<T: Debug>(f: &mut Formatter<'_>, els: &[T], indent: usize) -> FmtResult {
    let indent = indent + 2;
    for (idx, el) in els.iter().enumerate() {
        write!(f, "  {el:indent$?}")?;
        if idx < els.len() - 1 {
            write!(f, ",")?;
        }
        writeln!(f)?;
        f.pad("")?;
    }
    Ok(())
}
// fn indent(s: String) -> String {
//     s.split("\n").intersperse("\n  ").collect::<String>()
// }

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
        write!(
            f,
            ") {} (",
            match self.kind {
                BinOpKind::CmpEq => "==",
                BinOpKind::CmpNe => "!=",
                BinOpKind::CmpGt => ">",
                BinOpKind::CmpGe => ">=",
                BinOpKind::CmpLt => "<",
                BinOpKind::CmpLe => "<=",
                BinOpKind::And => "&&",
                BinOpKind::Or => "||",
                BinOpKind::Implies => "==>",
                BinOpKind::Add => "+",
                BinOpKind::Sub => "-",
                BinOpKind::Mul => "*",
                BinOpKind::Div => "\\",
                BinOpKind::PermAdd => "+",
                BinOpKind::PermSub => "-",
                BinOpKind::PermMul => "*",
                BinOpKind::PermPermDiv => "/",
                BinOpKind::Mod => "%",
            }
        )?;
        self.rhs.fmt(f)?;
        write!(f, ")")
    }
}

impl<'vir, Curr, Next> Debug for CollectionBinOpGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        let infix = match self.kind {
            CollectionBinOpKind::Index => {
                return write!(f, "{:?}[{:?}]", self.lhs, self.rhs);
            }
            CollectionBinOpKind::Take => {
                return write!(f, "{:?}[..{:?}]", self.lhs, self.rhs);
            }
            CollectionBinOpKind::Drop => {
                return write!(f, "{:?}[{:?}..]", self.lhs, self.rhs);
            }
            CollectionBinOpKind::Contains => "in",
            CollectionBinOpKind::Union => "union",
            CollectionBinOpKind::Intersection => "intersection",
            CollectionBinOpKind::Difference => "setminus",
            CollectionBinOpKind::Subset => "subset",
            CollectionBinOpKind::Concat => "++",
        };
        write!(f, "({:?} {infix} {:?})", self.lhs, self.rhs)
    }
}

impl<'vir> Debug for CfgBlockLabelData<'vir> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", self.name())
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

impl<'vir, Curr, Next> Debug for CfgLabelGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        writeln!(f, "label {:?}", self.label)?;
        for inv in self.invariants {
            writeln!(f, "  invariant {inv:?}")?;
        }
        Ok(())
    }
}

impl<'vir, Curr, Next> Debug for DomainGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "domain {}", self.name)?;
        if !self.typarams.is_empty() {
            write!(f, "[")?;
            fmt_comma_sep_display(f, self.typarams)?;
            write!(f, "]")?;
        }
        writeln!(f, " {{")?;
        self.axioms.iter().try_for_each(|el| el.fmt(f))?;
        self.functions.iter().try_for_each(|el| el.fmt(f))?;
        writeln!(f, "}}")
    }
}

impl<'vir, Curr, Next> Debug for DomainAxiomGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        writeln!(f, "  axiom {} {{", self.name)?;
        writeln!(f, "    {:4?}", self.expr)?;
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
        fmt_comma_sep(f, self.args)?;
        writeln!(f, "): {:?}", self.ret)
    }
}

impl<'vir, Curr, Next> Debug for AdtGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "adt {}", self.name)?;
        if !self.typarams.is_empty() {
            write!(f, "[")?;
            fmt_comma_sep_display(f, self.typarams)?;
            write!(f, "]")?;
        }
        writeln!(f, " {{")?;
        self.constructors.iter().try_for_each(|c| c.fmt(f))?;
        writeln!(f, "}}")
    }
}

impl<'vir, Curr, Next> Debug for AdtConstructorGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        assert!(self.axiom.is_none());
        write!(f, "  {}(", self.name)?;
        fmt_comma_sep(f, self.args)?;
        writeln!(f, ")")
    }
}

impl<'vir, Curr, Next, T: CompType> Debug for ExprGenData<'vir, Curr, Next, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        if let Some(span) = self.span {
            write!(f, "/*p:{}*/", span.id)?;
        }
        self.kind.fmt(f)
    }
}

impl<'vir, Curr, Next> Debug for ExprKindGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self::AccField(e) => e.fmt(f),
            Self::BinOp(e) => e.fmt(f),
            Self::CollectionBinOp(e) => e.fmt(f),
            Self::Const(e) => e.fmt(f),
            Self::Result(_) => write!(f, "result"),
            Self::Field(e, field) => write!(f, "{:?}.{}", e, field.name),
            Self::Forall(e) => e.fmt(f),
            Self::Exists(e) => e.fmt(f),
            Self::CollectionLiteral(e) => e.fmt(f),
            Self::CollectionUpdate(e) => write!(f, "{:?}[{:?} := {:?}]", e.target, e.key, e.val),
            Self::CollectionLen(e) => write!(f, "|{e:?}|"),
            Self::MapDomain(e) => write!(f, "domain({e:?})"),
            Self::MapRange(e) => write!(f, "range({e:?})"),
            Self::FuncApp(e) => e.fmt(f),
            Self::Let(e) => e.fmt(f),
            Self::InhaleExhale(e) => write!(f, "[{:?}, {:?}]", e.inhale, e.exhale),
            Self::Lazy(e) => write!(f, "%%/*{}*/", e.name),
            Self::Local(e) => e.fmt(f),
            Self::Old(e) => e.fmt(f),
            Self::PredicateApp(e) => e.fmt(f),
            Self::Wand(e) => e.fmt(f),
            Self::Ternary(e) => e.fmt(f),
            Self::UnOp(e) => e.fmt(f),
            Self::Unfolding(e) => e.fmt(f),
            Self::AdtDestructor(e, field) => write!(f, "{:?}.{}", e, field.name),
            Self::AdtDiscriminator(e, cons) => write!(f, "{e:?}.is{cons}"),
            Self::Todo(e) => write!(f, "{e}"),
        }
    }
}

impl<'vir, T: CompType> Debug for FieldData<'vir, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        writeln!(f, "field {}: {:?}", self.name, self.ty)
    }
}

impl<'vir, Curr, Next> Debug for ForallGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "forall ")?;
        fmt_comma_sep(f, self.qvars)?;
        write!(f, " ::")?;
        for trigger in self.triggers {
            write!(f, " {trigger:?}")?;
        }
        write!(f, " {:?}", self.body)
    }
}

impl<'vir, Curr, Next> Debug for ExistsGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "exists ")?;
        fmt_comma_sep(f, self.qvars)?;
        write!(f, " ::")?;
        for trigger in self.triggers {
            write!(f, " {trigger:?}")?;
        }
        write!(f, " {:?}", self.body)
    }
}

impl<'vir, Curr, Next> Debug for CollectionLiteralGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        if self.values.is_empty() {
            // The empty literal names its full type, e.g. `Seq[Int]()`.
            return write!(f, "{:?}()", self.ty);
        }
        let name = match self.ty.kind() {
            TypeKind::Seq(_) => "Seq",
            TypeKind::Map(..) => "Map",
            TypeKind::Multiset(_) => "Multiset",
            _ => "Set",
        };
        write!(f, "{name}(")?;
        fmt_comma_sep(f, self.values)?;
        write!(f, ")")
    }
}

impl<'vir, Curr, Next> Debug for FuncAppGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}(", self.target)?;
        fmt_comma_sep(f, self.args)?;
        write!(f, ")")?;
        Ok(())
    }
}

impl<'vir, Curr, Next> Debug for FunctionGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        writeln!(f, "function {}(", self.name)?;
        fmt_comma_sep_lines(f, self.args, 0)?;
        writeln!(f, "): {:?}", self.ret)?;
        self.pres
            .iter()
            .try_for_each(|el| writeln!(f, "  requires {el:?}"))?;
        self.posts
            .iter()
            .try_for_each(|el| writeln!(f, "  ensures {el:?}"))?;
        if let Some(expr) = self.expr {
            writeln!(f, "{{\n  {expr:2?}\n}}")?;
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
        let indent = f.width().unwrap_or_default();
        writeln!(f, "(let {} == ({:indent$?}) in", self.name, self.val)?;
        f.pad("")?;
        let indent = indent + 2;
        write!(f, "  {:indent$?})", self.expr)
    }
}

impl<'vir, T: CompType> Debug for LocalData<'vir, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", self.name)
    }
}

impl<'vir, T: CompType> Debug for LocalDeclData<'vir, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}: ", self.name)?;
        self.ty.fmt(f)?;
        Ok(())
    }
}

impl<'vir, Curr, Next> Debug for MethodGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        writeln!(f, "method {}(", self.name)?;
        fmt_comma_sep_lines(f, self.args, 0)?;
        if !self.rets.is_empty() {
            writeln!(f, ") returns (")?;
            fmt_comma_sep_lines(f, self.rets, 0)?;
            writeln!(f, ")")?;
        } else {
            writeln!(f, ")")?;
        }
        self.pres
            .iter()
            .try_for_each(|el| writeln!(f, "  requires {el:2?}"))?;
        self.posts
            .iter()
            .try_for_each(|el| writeln!(f, "  ensures {el:2?}"))?;
        if let Some(body) = self.body.as_ref() {
            writeln!(f, "{{")?;
            for block in body.blocks.iter() {
                write!(f, "{:?}", block.label)?;
                for stmt in block.stmts {
                    writeln!(f, "  {stmt:2?}")?;
                }
                writeln!(f, "  {:2?}", block.terminator)?;
            }
            writeln!(f, "}}")?;
        }
        Ok(())
    }
}

impl<'vir, Curr, Next> Debug for OldGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "old")?;
        match &self.label {
            OldLabel::None => (),
            OldLabel::Lhs => write!(f, "[lhs]")?,
            OldLabel::Block(block) => block.fmt(f)?,
            OldLabel::Label(l) => write!(f, "[{l}]")?,
        }
        write!(f, "(")?;
        self.expr.fmt(f)?;
        write!(f, ")")
    }
}

impl<'vir, Curr, Next> Debug for PredicateGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "predicate {}(", self.name)?;
        fmt_comma_sep(f, self.args)?;
        write!(f, ")")?;
        if let Some(expr) = self.expr {
            writeln!(f, "{{\n  {expr:2?}\n}}")
        } else {
            writeln!(f)
        }
    }
}

impl<'vir, Curr, Next> Debug for PredicateAppGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        if self.perm.is_some() {
            write!(f, "acc(")?;
        }
        write!(f, "{}(", self.target)?;
        fmt_comma_sep(f, self.args)?;
        write!(f, ")")?;
        if let Some(perm) = self.perm {
            write!(f, ", {perm:?})")?;
        }
        Ok(())
    }
}

impl<'vir, Curr, Next> Debug for StmtGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        if let Some(span) = self.span {
            write!(f, "/*p:{}*/", span.id)?;
        }
        self.kind.fmt(f)
    }
}

impl<'vir, Curr, Next> Debug for StmtKindGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        let indent = f.width().unwrap_or_default();
        match self {
            Self::LocalDecl(decl, expr) => {
                write!(f, "var {decl:indent$?}")?;
                if let Some(expr) = expr {
                    write!(f, " := {expr:indent$?}")?;
                }
                Ok(())
            }
            Self::PureAssign(data) => write!(f, "{:indent$?} := {:indent$?}", data.lhs, data.rhs),
            Self::Inhale(data) => write!(f, "inhale {data:indent$?}"),
            Self::Exhale(data) => write!(f, "exhale {data:indent$?}"),
            Self::Refute(data) => write!(f, "refute {data:indent$?}"),
            Self::Unfold(data) => write!(f, "unfold {data:indent$?}"),
            Self::Fold(data) => write!(f, "fold {data:indent$?}"),
            Self::Package(wand, stmts) => {
                writeln!(f, "package {wand:?} {{")?;
                f.pad("")?;
                let indent = indent + 2;
                for stmt in stmts.iter() {
                    writeln!(f, "  {stmt:indent$?}")?;
                    f.pad("")?;
                }
                write!(f, "}}")
            }
            Self::Apply(wand) => write!(f, "apply {wand:indent$?}"),
            Self::MethodCall(data) => {
                if !data.targets.is_empty() {
                    fmt_comma_sep(f, data.targets)?;
                    write!(f, " := ")?;
                }
                write!(f, "{}(", data.method)?;
                fmt_comma_sep(f, data.args)?;
                write!(f, ")")
            }
            Self::If(e, thn, els) => {
                writeln!(f, "if ({e:indent$?}) {{")?;
                f.pad("")?;
                let indent = indent + 2;
                for stmt in thn.iter() {
                    writeln!(f, "  {stmt:indent$?}")?;
                    f.pad("")?;
                }
                if !els.is_empty() {
                    writeln!(f, "}} else {{")?;
                    for stmt in els.iter() {
                        writeln!(f, "  {stmt:indent$?}")?;
                        f.pad("")?;
                    }
                }
                write!(f, "}}")
            }
            Self::Label(label) => write!(f, "label {label}"),
            Self::Comment(info) => write!(f, "// {info}"),
            Self::Dummy(info) => write!(f, "// {info}"),
        }
    }
}

impl<'vir, Curr, Next> Debug for TerminatorStmtGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        let indent = f.width().unwrap_or_default();
        match self {
            Self::AssumeFalse => {
                writeln!(f, "assume false")?;
                f.pad("")?;
                write!(f, "{:?}", Self::Goto(&CfgBlockLabelData::End))
            }
            Self::Goto(target) => write!(f, "goto {target:?}"),
            Self::GotoIf(data) => {
                if data.targets.is_empty() {
                    for extra in data.otherwise_statements {
                        write!(f, "{extra:indent$?}")?;
                    }
                    write!(f, "goto {:?}", data.otherwise)
                } else {
                    for target in data.targets {
                        writeln!(
                            f,
                            "if ({:indent$?} == {:indent$?}) {{",
                            data.value, target.value
                        )?;
                        f.pad("")?;
                        let indent = indent + 2;
                        for extra in target.statements {
                            writeln!(f, "  {extra:indent$?}")?;
                            f.pad("")?;
                        }
                        writeln!(f, "  goto {:?}", target.label)?;
                        f.pad("")?;
                        write!(f, "}} else")?;
                    }
                    writeln!(f, " {{")?;
                    let indent = indent + 2;
                    for extra in data.otherwise_statements {
                        writeln!(f, "  {extra:indent$?}")?;
                        f.pad("")?;
                    }
                    writeln!(f, "  goto {:?}", data.otherwise)?;
                    f.pad("")?;
                    write!(f, "}}")
                }
            }
            Self::Exit => write!(f, "// return"),
            Self::Dummy(info) => {
                writeln!(f, "assert false // {info}")?;
                f.pad("")?;
                write!(f, "{:?}", Self::Goto(&CfgBlockLabelData::End))
            }
        }
    }
}

impl<'vir, Curr, Next> Debug for TernaryGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        let indent = f.width().unwrap_or_default();
        writeln!(f, "{:indent$?}", self.cond)?;
        f.pad("")?;
        let indent = indent + 2;
        writeln!(f, "? {:indent$?}", self.then)?;
        f.pad("")?;
        write!(f, ": {:indent$?}", self.else_)
    }
}

impl<'vir, Curr, Next> Debug for TriggerGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{{")?;
        fmt_comma_sep(f, self.exprs)?;
        write!(f, "}}")
    }
}

impl<'vir, T: CompType> Debug for TypeData<'vir, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        (**self).fmt(f)
    }
}

impl<'vir> Debug for TypeKind<'vir> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self::Int { .. } => write!(f, "Int"),
            Self::Bool => write!(f, "Bool"),
            Self::DomainTypeParam(name) => write!(f, "{name}"),
            Self::Domain(name, params) => {
                write!(f, "{name}")?;
                if !params.is_empty() {
                    write!(f, "[")?;
                    fmt_comma_sep(f, params)?;
                    write!(f, "]")?;
                }
                Ok(())
            }
            Self::Ref => write!(f, "Ref"),
            Self::Perm => write!(f, "Perm"),
            Self::Set(ty) => write!(f, "Set[{ty:?}]"),
            Self::Multiset(ty) => write!(f, "Multiset[{ty:?}]"),
            Self::Seq(ty) => write!(f, "Seq[{ty:?}]"),
            Self::Map(key, val) => write!(f, "Map[{key:?}, {val:?}]"),
            Self::Unsupported(u) => u.fmt(f),
            Self::Err => write!(f, "Err"),
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
        write!(
            f,
            "{}({:?})",
            match self.kind {
                UnOpKind::Neg => "-",
                UnOpKind::PermNeg => "-",
                UnOpKind::Not => "!",
            },
            self.expr
        )
    }
}

impl<'vir, Curr, Next> Debug for UnfoldingGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "unfolding {:?} in ({:?})", self.target, self.expr)
    }
}

impl<'vir, Curr, Next> Debug for WandGenData<'vir, Curr, Next> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "({:?}) --* ({:?})", self.lhs, self.rhs)
    }
}
