#![feature(rustc_private)]
#![feature(associated_type_defaults)]
#![feature(once_cell)]
#![feature(iter_intersperse)]
#![feature(local_key_cell_methods)]
#![feature(box_patterns)]

extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_type_ir;

mod encoders;

use prusti_rustc_interface::{
    middle::ty,
    hir,
};

#[allow(unused)]
mod vir {
    use std::fmt::{Debug, Formatter, Result as FmtResult};
    use prusti_rustc_interface::middle::ty;
    pub use bumpalo::collections::Vec as BumpVec;
    pub use bumpalo::vec as bvec;

    // TODO: most (all?) vectors in the Data definitions should be slices

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

    // for all arena-allocated types, there are two type definitions: one with
    // a `Data` suffix, containing the actual data; and one without the suffix,
    // being shorthand for a VIR-lifetime reference to the data.

    pub struct LocalData<'vir> {
        pub name: &'vir str, // TODO: identifiers
    }
    impl<'vir> Debug for LocalData<'vir> {
        fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
            write!(f, "{}", self.name)
        }
    }
    pub type Local<'vir> = &'vir LocalData<'vir>;

    #[derive(Debug)]
    pub enum UnOpKind {
        Neg,
        Not,
    }
    pub struct UnOpData<'vir> {
        pub kind: UnOpKind,
        pub expr: Expr<'vir>,
    }
    impl<'vir> Debug for UnOpData<'vir> {
        fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
            write!(f, "{}({:?})", match self.kind {
                UnOpKind::Neg => "-",
                UnOpKind::Not => "!",
            }, self.expr)
        }
    }
    pub type UnOp<'vir> = &'vir UnOpData<'vir>;

    #[derive(Debug)]
    pub enum BinOpKind {
        CmpEq,
        And,
        // ...
    }
    pub struct BinOpData<'vir> {
        pub kind: BinOpKind,
        pub lhs: Expr<'vir>,
        pub rhs: Expr<'vir>,
    }
    impl<'vir> Debug for BinOpData<'vir> {
        fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
            write!(f, "(")?;
            self.lhs.fmt(f)?;
            write!(f, ") {} (", match self.kind {
                BinOpKind::CmpEq => "==",
                BinOpKind::And => "&&",
            })?;
            self.rhs.fmt(f)?;
            write!(f, ")")
        }
    }
    pub type BinOp<'vir> = &'vir BinOpData<'vir>;

    pub struct TernaryData<'vir> {
        pub cond: Expr<'vir>,
        pub then: Expr<'vir>,
        pub else_: Expr<'vir>,
    }
    impl<'vir> Debug for TernaryData<'vir> {
        fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
            write!(f, "{:?} ? {:?} : {:?}", self.cond, self.then, self.else_)
        }
    }
    pub type Ternary<'vir> = &'vir TernaryData<'vir>;

    pub struct ForallData<'vir> {
        pub qvars: BumpVec<'vir, LocalDecl<'vir>>,
        pub triggers: BumpVec<'vir, Expr<'vir>>,
        pub body: Expr<'vir>,
    }
    impl<'vir> Debug for ForallData<'vir> {
        fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
            write!(f, "forall ")?;
            fmt_comma_sep(f, &self.qvars)?;
            write!(f, " :: {{")?;
            fmt_comma_sep(f, &self.triggers)?;
            write!(f, "}} {:?}", self.body)
        }
    }
    pub type Forall<'vir> = &'vir ForallData<'vir>;

    pub struct FuncAppData<'vir> {
        pub target: &'vir str, // TODO: identifiers
        pub args: BumpVec<'vir, Expr<'vir>>,
    }
    impl<'vir> Debug for FuncAppData<'vir> {
        fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
            write!(f, "{}(", self.target)?;
            fmt_comma_sep(f, &self.args)?;
            write!(f, ")")
        }
    }
    pub type FuncApp<'vir> = &'vir FuncAppData<'vir>;

    pub struct PredicateAppData<'vir> {
        pub target: &'vir str, // TODO: identifiers
        pub args: BumpVec<'vir, Expr<'vir>>,
    }
    impl<'vir> Debug for PredicateAppData<'vir> {
        fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
            write!(f, "{}(", self.target)?;
            fmt_comma_sep(f, &self.args)?;
            write!(f, ")")
        }
    }
    pub type PredicateApp<'vir> = &'vir PredicateAppData<'vir>;

    pub enum ExprData<'vir> {
        Local(Local<'vir>),
        //Field(Expr<'vir>, &'vir str),
        //LabelledOld(Expr<'vir>, &'vir str),
        // const
        // magic wand
        // acc(..)
        // unfolding ..
        UnOp(UnOp<'vir>),
        BinOp(BinOp<'vir>),
        // perm ops?
        // container ops?
        // map ops?
        // sequence, map, set, multiset literals
        Ternary(Ternary<'vir>),
        Forall(Forall<'vir>),
        // let
        FuncApp(FuncApp<'vir>),
        PredicateApp(PredicateApp<'vir>),
        // domain func app
        // inhale/exhale

        Todo(&'vir str),
    }
    impl<'vir> Debug for ExprData<'vir> {
        fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
            match self {
                Self::Local(e) => e.fmt(f),
                Self::UnOp(e) => e.fmt(f),
                Self::BinOp(e) => e.fmt(f),
                Self::Ternary(e) => e.fmt(f),
                Self::Forall(e) => e.fmt(f),
                Self::FuncApp(e) => e.fmt(f),
                Self::PredicateApp(e) => e.fmt(f),
                Self::Todo(e) => write!(f, "{}", e),
            }
        }
    }
    // + position, meta?
    pub type Expr<'vir> = &'vir ExprData<'vir>;

    pub enum TypeData<'vir> {
        Int,
        Bool,
        Domain(&'vir str), // TODO: identifiers
        Ref, // TODO: typed references ?
    }
    impl<'vir> Debug for TypeData<'vir> {
        fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
            match self {
                Self::Int => write!(f, "Int"),
                Self::Bool => write!(f, "Bool"),
                Self::Domain(name) => write!(f, "{}", name),
                Self::Ref => write!(f, "Ref"),
            }
        }
    }
    pub type Type<'vir> = &'vir TypeData<'vir>;

    pub struct LocalDeclData<'vir> {
        pub name: &'vir str, // TODO: identifiers
        pub ty: Type<'vir>,
        pub expr: Option<Expr<'vir>>, // TODO: does this belong into StmtData?
    }
    impl<'vir> Debug for LocalDeclData<'vir> {
        fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
            write!(f, "{}: ", self.name)?;
            self.ty.fmt(f)?;
            if let Some(expr) = self.expr {
                write!(f, " := {:?}", expr)?;
            }
            Ok(())
        }
    }
    pub type LocalDecl<'vir> = &'vir LocalDeclData<'vir>;

    pub struct DomainAxiomData<'vir> {
        pub name: &'vir str, // ? or comment, then auto-gen the names?
        pub expr: Expr<'vir>,
    }
    impl<'vir> Debug for DomainAxiomData<'vir> {
        fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
            writeln!(f, "  axiom {} {{", self.name)?;
            writeln!(f, "    {:?}", self.expr)?;
            writeln!(f, "  }}")
        }
    }
    pub type DomainAxiom<'vir> = &'vir DomainAxiomData<'vir>;

    pub struct DomainFunctionData<'vir> {
        pub unique: bool,
        pub name: &'vir str, // TODO: identifiers
        pub args: BumpVec<'vir, Type<'vir>>,
        pub ret: Type<'vir>,
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
    pub type DomainFunction<'vir> = &'vir DomainFunctionData<'vir>;

    pub struct DomainData<'vir> {
        pub name: &'vir str, // TODO: identifiers
        pub axioms: BumpVec<'vir, DomainAxiom<'vir>>,
        pub functions: BumpVec<'vir, DomainFunction<'vir>>,
    }
    impl<'vir> Debug for DomainData<'vir> {
        fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
            writeln!(f, "domain {} {{", self.name)?;
            self.axioms.iter().map(|el| el.fmt(f)).collect::<FmtResult>()?;
            self.functions.iter().map(|el| el.fmt(f)).collect::<FmtResult>()?;
            writeln!(f, "}}")
        }
    }
    pub type Domain<'vir> = &'vir DomainData<'vir>;

    pub struct PredicateData<'vir> {
        pub name: &'vir str, // TODO: identifiers
        pub args: BumpVec<'vir, LocalDecl<'vir>>,
        pub expr: Option<Expr<'vir>>,
    }
    impl<'vir> Debug for PredicateData<'vir> {
        fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
            write!(f, "predicate {}(", self.name)?;
            fmt_comma_sep(f, &self.args)?;
            write!(f, ")")?;
            if let Some(expr) = self.expr {
                write!(f, " {{\n  ")?;
                expr.fmt(f);
                writeln!(f, "\n}}")
            } else {
                writeln!(f, "")
            }
        }
    }
    pub type Predicate<'vir> = &'vir PredicateData<'vir>;

    pub struct FunctionData<'vir> {
        pub name: &'vir str, // TODO: identifiers
        pub args: BumpVec<'vir, LocalDecl<'vir>>,
        pub ret: Type<'vir>,
        pub pres: BumpVec<'vir, Expr<'vir>>,
        pub posts: BumpVec<'vir, Expr<'vir>>,
        pub expr: Option<Expr<'vir>>,
    }
    impl<'vir> Debug for FunctionData<'vir> {
        fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
            writeln!(f, "function {}(", self.name)?;
            fmt_comma_sep_lines(f, &self.args)?;
            writeln!(f, "): {:?}", self.ret)?;
            self.pres.iter().map(|el| writeln!(f, "  requires {:?}", el)).collect::<FmtResult>()?;
            self.posts.iter().map(|el| writeln!(f, "  ensures {:?}", el)).collect::<FmtResult>()?;
            if let Some(expr) = self.expr {
                write!(f, "{{\n  ")?;
                expr.fmt(f);
                writeln!(f, "\n}}")?;
            }
            Ok(())
        }
    }
    pub type Function<'vir> = &'vir FunctionData<'vir>;

    pub struct PureAssignData<'vir> {
        pub dest: Local<'vir>,
        pub expr: Expr<'vir>,
    }
    pub type PureAssign<'vir> = &'vir PureAssignData<'vir>;

    pub struct MethodCallData<'vir> {
        pub targets: BumpVec<'vir, Local<'vir>>,
        pub method: &'vir str,
        pub args: BumpVec<'vir, Expr<'vir>>,
    }
    pub type MethodCall<'vir> = &'vir MethodCallData<'vir>;

    pub enum StmtData<'vir> {
        LocalDecl(LocalDecl<'vir>),
        PureAssign(PureAssign<'vir>),
        Inhale(Expr<'vir>),
        Exhale(Expr<'vir>),
        MethodCall(MethodCall<'vir>),
        Comment(&'vir str),
        Dummy(&'vir str),
    }
    impl<'vir> Debug for StmtData<'vir> {
        fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
            match self {
                Self::LocalDecl(data) => write!(f, "var {:?}", data),
                Self::PureAssign(data) => write!(f, "{:?} := {:?}", data.dest, data.expr),
                Self::Inhale(data) => write!(f, "inhale {:?}", data),
                Self::Exhale(data) => write!(f, "exhale {:?}", data),
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
    pub type Stmt<'vir> = &'vir StmtData<'vir>;

    pub struct GotoIfData<'vir> {
        pub value: Expr<'vir>,
        pub targets: BumpVec<'vir, (Expr<'vir>, CfgBlockLabel<'vir>)>,
        pub otherwise: CfgBlockLabel<'vir>,
    }
    pub type GotoIf<'vir> = &'vir GotoIfData<'vir>;

    pub enum TerminatorStmtData<'vir> {
        AssumeFalse,
        Goto(CfgBlockLabel<'vir>),
        GotoIf(GotoIf<'vir>),
        Exit,
        Dummy(&'vir str),
    }
    impl<'vir> Debug for TerminatorStmtData<'vir> {
        fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
            match self {
                Self::AssumeFalse => write!(f, "assume false"),
                Self::Goto(target) => write!(f, "goto {:?}", target),
                Self::GotoIf(data) => {
                    if data.targets.is_empty() {
                        write!(f, "goto {:?}", data.otherwise)
                    } else {
                        for target in &data.targets {
                            write!(f, "if ({:?} == {:?}) {{ goto {:?} }}\n  else", data.value, target.0, target.1)?;
                        }
                        write!(f, " {{ goto {:?} }}", data.otherwise)
                    }
                }
                Self::Exit => write!(f, "// return"),
                Self::Dummy(info) => write!(f, "// {}", info),
            }
        }
    }
    pub type TerminatorStmt<'vir> = &'vir TerminatorStmtData<'vir>;

    pub enum CfgBlockLabelData {
        Start,
        End,
        BasicBlock(usize),
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
    pub type CfgBlockLabel<'vir> = &'vir CfgBlockLabelData;

    #[derive(Debug)]
    pub struct CfgBlockData<'vir> {
        pub label: CfgBlockLabel<'vir>,
        pub stmts: BumpVec<'vir, Stmt<'vir>>,
        pub terminator: TerminatorStmt<'vir>,
    }
    pub type CfgBlock<'vir> = &'vir CfgBlockData<'vir>;

    pub struct MethodData<'vir> {
        pub name: &'vir str, // TODO: identifiers
        pub args: BumpVec<'vir, LocalDecl<'vir>>,
        pub rets: BumpVec<'vir, LocalDecl<'vir>>,
        pub pres: BumpVec<'vir, Expr<'vir>>,
        pub posts: BumpVec<'vir, Expr<'vir>>,
        pub blocks: Option<BumpVec<'vir, CfgBlock<'vir>>>, // first one is the entrypoint
    }
    impl<'vir> Debug for MethodData<'vir> {
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
                    for stmt in &block.stmts {
                        writeln!(f, "  {:?}", stmt)?;
                    }
                    writeln!(f, "  {:?}", block.terminator)?;
                }
                writeln!(f, "}}")?;
            }
            Ok(())
        }
    }
    pub type Method<'vir> = &'vir MethodData<'vir>;

    #[derive(Debug)]
    pub struct ProgramData<'vir> {
        pub domains: BumpVec<'vir, Domain<'vir>>,
        pub predicates: BumpVec<'vir, Predicate<'vir>>,
        pub functions: BumpVec<'vir, Function<'vir>>,
        pub methods: BumpVec<'vir, Method<'vir>>,
        // verification flags?
    }
    pub type Program<'vir> = &'vir ProgramData<'vir>;

    pub struct VirCtxt<'tcx> {
        pub arena: bumpalo::Bump,
        pub span_stack: Vec<i32>,
        // TODO: span stack
        // TODO: error positions?
        pub tcx: ty::TyCtxt<'tcx>,
    }
    impl<'tcx> VirCtxt<'tcx> {
        pub fn new(tcx: ty::TyCtxt<'tcx>) -> Self {
            Self {
                arena: bumpalo::Bump::new(),
                span_stack: vec![],
                tcx,
            }
        }
        pub fn alloc<T>(&self, val: T) -> &T {
            &*self.arena.alloc(val)
        }
        pub fn alloc_str(&self, val: &str) -> &str {
            &*self.arena.alloc_str(val)
        }

        pub fn mk_local<'vir>(&'vir self, name: &'vir str) -> Local<'vir> {
            self.arena.alloc(LocalData {
                name,
            })
        }
        pub fn mk_local_decl<'vir>(&'vir self, name: &'vir str, ty: Type<'vir>) -> LocalDecl<'vir> {
            self.arena.alloc(LocalDeclData {
                name,
                ty,
                expr: None,
            })
        }
        pub fn mk_local_ex<'vir>(&'vir self, name: &'vir str) -> Expr<'vir> {
            self.arena.alloc(ExprData::Local(self.mk_local(name)))
        }

        pub fn mk_func_app<'vir>(&'vir self, target: &'vir str, src_args: &[Expr<'vir>]) -> Expr<'vir> {
            let mut args = BumpVec::with_capacity_in(src_args.len(), &self.arena);
            args.extend_from_slice(&src_args);
            self.arena.alloc(ExprData::FuncApp(self.arena.alloc(FuncAppData {
                target,
                args,
            })))
        }
    }
}

//use lazy_static::lazy_static;
use std::cell::RefCell;
thread_local! {
    static VCTX: RefCell<Option<vir::VirCtxt<'static>>> = RefCell::new(None); // Some(vir::VirCtxt::new());
}
fn with_vcx<'vir, 'tcx, F, R>(f: F) -> R
where
    F: FnOnce(&'vir vir::VirCtxt<'vir>) -> R,
{
    VCTX.with_borrow(|vcx: &Option<vir::VirCtxt<'static>>| {
        // SAFETY: the 'vir and 'tcx given to this function will always be
        //   the same (or shorter) than the lifetimes of the VIR arena and
        //   the rustc type context, respectively
        let vcx = vcx.as_ref().unwrap();
        let vcx = unsafe { std::mem::transmute(vcx) };
        f(vcx)
    })
    /*VCTX.with(|vcx: &Cell<Option<vir::VirCtxt>>| {
        // SAFETY: the 'vir and 'tcx given to this function will always be
        //   the same (or shorter) than the lifetimes of the VIR arena and
        //   the rustc type context, respectively
        let vcx = vcx.as_ref().unwrap();
        let vcx = unsafe { std::mem::transmute(vcx) };
        f(vcx)
    })*/
}

//#[macro_export]
//macro_rules! vir_expr_nopos {
//    
//}

//#[macro_export]
//macro_rules! vir {
//    ($vcx: expr, $span: expr, $ops: tt) => {
//        $vcx.enter($span, |spanned_vcx| $ops)
//    };
//}

#[macro_export]
macro_rules! vir_span {
    ($vcx: expr, $span: expr, $ops: tt) => {{
        $vcx.span_stack.push($span);
        let result = $ops;
        $vcx.span_stack.pop();
        result
    }};
}

#[macro_export]
macro_rules! vir_type_list {
    ($vcx:expr; $( $args:tt ),* $(,)? ) => {{
        #[allow(unused_mut)]
        let mut v = bumpalo::collections::Vec::new_in(&$vcx.arena);
        $( v.push($crate::vir_type!($vcx; $args)); )*
        v
    }};
}

#[macro_export]
macro_rules! vir_arg_list {
    ($vcx:expr; $( $name:tt : $ty:tt ),* $(,)? ) => {{
        #[allow(unused_mut)]
        let mut v = bumpalo::collections::Vec::new_in(&$vcx.arena);
        $( v.push($crate::vir_local_decl!($vcx; $name : $ty)); )*
        v
    }};
}

/*
#[macro_export]
macro_rules! vir_expr_list {
    ($vcx:expr; $( $args:tt ),* $(,)? ) => {{
        let mut v = bumpalo::collections::Vec::new_in(&$vcx.arena);
        $( println!("expr list arg: {}", stringify!($args)); )*
        $( v.push($crate::vir_expr!($vcx; $args)); )*
        v
    }};
}

// TODO: $crate:: for vir as well?
#[macro_export]
macro_rules! vir_expr {
    ($vcx:expr; forall([ $( $args:tt )* ] $( $body:tt )*)) => {{
        &*$vcx.arena.alloc(vir::ExprData::Forall(&*$vcx.arena.alloc(vir::ForallData {
            qvars: bumpalo::vec![in &$vcx.arena],
            // triggers
            body: $crate::vir_expr!($vcx; $($body)*),
        })))
    }};
    ($vcx:expr; $target:ident ( $($args:tt),* )) => {{
        // TODO: arguments ...
        &*$vcx.arena.alloc(vir::ExprData::FuncApp(&*$vcx.arena.alloc(vir::FuncAppData {
            target: $vcx.alloc_str(stringify!($target)), // TODO: vir_ident
            args: $crate::vir_expr_list!($vcx; $($args)*),
            //args: bumpalo::vec![in &$vcx.arena; $( $crate::vir_expr!($vcx; $args) ),* ],
        })))
    }};
    ($vcx:expr; $name:ident) => {{
        &*$vcx.arena.alloc(vir::ExprData::Local(&*$vcx.arena.alloc(vir::LocalData {
            name: $vcx.alloc_str(stringify!($name)), // TODO: vir_ident
        })))
    }};
    ($vcx:expr; ($($lhs:tt)*) == ($($rhs:tt)*)) => {{
        &*$vcx.arena.alloc(vir::ExprData::BinOp(&*$vcx.arena.alloc(vir::BinOpData {
            kind: vir::BinOpKind::CmpEq,
            lhs: $crate::vir_expr!($vcx; $($lhs)*),
            rhs: $crate::vir_expr!($vcx; $($rhs)*),
        })))
    }};
    ($vcx:expr; ($($e:tt)*)) => {{
        $crate::vir_expr!($vcx; $($e)*)
    }};

    /*
    ($vcx: expr, foo) => {{
        assert!(!$vcx.span_stack.is_empty());
        &*$vcx.arena.alloc(vir::ExprData::Foo)
    }};
    ($vcx: expr, ($lhs: tt) == ($rhs: tt)) => {{
        assert!(!$vcx.span_stack.is_empty());
        &*$vcx.arena.alloc(vir::ExprData::EqCmp($crate::vir_expr!($vcx, $lhs), $crate::vir_expr!($vcx, $rhs)))
    }};
    ($vcx: expr, !($sub: tt)) => {{
        assert!(!$vcx.span_stack.is_empty());
        &*$vcx.arena.alloc(vir::ExprData::Neg($crate::vir_expr!($vcx, $sub)))
    }};*/
}
*/

#[macro_export]
macro_rules! vir_expr {
    ($vcx:expr; $( $args:tt )* ) => {
        &*$vcx.arena.alloc(vir::ExprData::Todo(
            $vcx.alloc_str(stringify!($($args)*)),
        ))
    }
}

#[macro_export]
macro_rules! vir_ident {
    ($vcx:expr; [ $name:expr ]) => { $name };
    ($vcx:expr; $name:ident ) => { $vcx.alloc_str(stringify!($name)) };
}

#[macro_export]
macro_rules! vir_format {
    ($vcx:expr, $($arg:tt)*) => { $vcx.alloc_str(&format!($($arg)*)) };
}

#[macro_export]
macro_rules! vir_type {
    ($vcx:expr; Int) => { $vcx.alloc($crate::vir::TypeData::Int) };
    ($vcx:expr; Bool) => { $vcx.alloc($crate::vir::TypeData::Bool) };
    ($vcx:expr; Ref) => { $vcx.alloc($crate::vir::TypeData::Ref) };
    ($vcx:expr; [ $ty:expr ]) => { $ty };
    ($vcx:expr; $name:ident) => {
        $vcx.alloc($crate::vir::TypeData::Domain($vcx.alloc_str(stringify!($name))))
    };
}

#[macro_export]
macro_rules! vir_local_decl {
    // TODO: x: T := expr
    ($vcx:expr; $name:tt : $ty:tt) => {
        $vcx.alloc($crate::vir::LocalDeclData {
            name: $crate::vir_ident!($vcx; $name),
            ty: $crate::vir_type!($vcx; $ty),
            expr: None,
        })
    };
}

#[macro_export]
macro_rules! vir_domain_axiom {
    ($vcx:expr; axiom_inverse($a:tt, $b:tt)) => {{
        let name = $vcx.alloc_str(&format!(
            "axiom_inverse_{}_{}",
            $crate::vir_ident!($vcx; $a),
            $crate::vir_ident!($vcx; $b),
        ));
        $crate::vir_domain_axiom!($vcx; axiom [name] { forall(|x: Bool| val(cons(x)) == x ) })
    }};
    ($vcx:expr; axiom $name:tt { $( $body:tt )* }) => {{
        $vcx.alloc($crate::vir::DomainAxiomData {
            name: $crate::vir_ident!($vcx; $name),
            expr: $crate::vir_expr!($vcx; $($body)*),
        })
    }};
}

#[macro_export]
macro_rules! vir_domain_func {
    ($vcx:expr; unique function $name:tt ( $( $args:tt )* ): $ret:tt ) => {{
        $vcx.alloc($crate::vir::DomainFunctionData {
            unique: true,
            name: $crate::vir_ident!($vcx; $name),
            args: $crate::vir_type_list!($vcx; $($args)*),
            ret: $crate::vir_type!($vcx; $ret),
        })
    }};
    ($vcx:expr; function $name:tt ( $( $args:tt )* ): $ret:tt ) => {{
        $vcx.alloc($crate::vir::DomainFunctionData {
            unique: false,
            name: $crate::vir_ident!($vcx; $name),
            args: $crate::vir_type_list!($vcx; $($args)*),
            ret: $crate::vir_type!($vcx; $ret),
        })
    }};
}

#[macro_export]
macro_rules! vir_domain_members {
    ($vcx:expr; $axioms:expr; $functions:expr;
        axiom_inverse($a:ident, $b:ident);
        $( $rest:tt )*
    ) => {{
        $axioms.push($crate::vir_domain_axiom!($vcx; axiom_inverse($a, $b)));
        $crate::vir_domain_members!($vcx; $axioms; $functions; $($rest)*);
    }};
    ($vcx:expr; $axioms:expr; $functions:expr;
        unique function $name:tt ( $( $args:tt )* ): $ret:tt;
        $( $rest:tt )*
    ) => {{
        $functions.push($crate::vir_domain_func!($vcx; unique function $name( $($args)* ): $ret));
        $crate::vir_domain_members!($vcx; $axioms; $functions; $($rest)*);
    }};
    ($vcx:expr; $axioms:expr; $functions:expr;
        function $name:tt ( $( $args:tt )* ): $ret:tt;
        $( $rest:tt )*
    ) => {{
        $functions.push($crate::vir_domain_func!($vcx; function $name( $($args)* ): $ret));
        $crate::vir_domain_members!($vcx; $axioms; $functions; $($rest)*);
    }};
    ($vcx:expr; $axioms:expr; $functions:expr;
        with_funcs [ $e:expr ];
        $( $rest:tt )*
    ) => {{
        $functions.extend($e);
        $crate::vir_domain_members!($vcx; $axioms; $functions; $($rest)*);
    }};
    ($vcx:expr; $axioms:expr; $functions:expr;
        with_axioms [ $e:expr ];
        $( $rest:tt )*
    ) => {{
        $axioms.extend($e);
        $crate::vir_domain_members!($vcx; $axioms; $functions; $($rest)*);
    }};
    ($vcx:expr; $axioms:expr; $functions:expr;) => {};
}

#[macro_export]
macro_rules! vir_domain {
    ($vcx:expr; domain $name:tt { $( $member:tt )* }) => {{
        #[allow(unused_mut)]
        let mut axioms = bumpalo::vec![in &$vcx.arena];
        #[allow(unused_mut)]
        let mut functions = bumpalo::vec![in &$vcx.arena];
        $crate::vir_domain_members!($vcx; axioms; functions; $($member)*);
        $vcx.alloc($crate::vir::DomainData {
            name: $crate::vir_ident!($vcx; $name),
            axioms,
            functions,
        })
    }};
}

#[macro_export]
macro_rules! vir_predicate {
    ($vcx:expr; predicate $name:tt ( $( $args:tt )* )) => {{
        $vcx.alloc($crate::vir::PredicateData {
            name: $crate::vir_ident!($vcx; $name),
            args: $crate::vir_arg_list!($vcx; $($args)*),
            expr: None,
        })
    }}
}

/*
struct MirBodyPureEncoder;
#[derive(Hash, Clone, PartialEq, Eq)]
enum MirBodyPureEncoderTask<'tcx> {
    Function {
        parent_def_id: ty::WithOptConstParam<DefId>, // ID of the function
        param_env: ty::ParamEnv<'tcx>, // param environment at the usage site
        substs: ty::SubstsRef<'tcx>, // type substitutions at the usage site
    },
    Constant {
        parent_def_id: ty::WithOptConstParam<DefId>, // ID of the function
        promoted: mir::Promoted, // ID of a constant within the function
        param_env: ty::ParamEnv<'tcx>, // param environment at the usage site
        substs: ty::SubstsRef<'tcx>, // type substitutions at the usage site
    },
}
// impl<'tcx> MirBodyPureEncoder {} // TODO: shortcuts for creating tasks?
impl TaskEncoder for MirBodyPureEncoder {
    type TaskDescription<'vir, 'tcx> = MirBodyPureEncoderTask<'tcx>;
    type TaskKey<'vir, 'tcx> = (
        DefId, // ID of the function
        Option<mir::Promoted>, // ID of a constant within the function, or `None` if encoding the function itself
        ty::SubstsRef<'tcx>, // ? this should be the "signature", after applying the env/substs
    );
    type OutputFullLocal<'vir, 'tcx> = vir::Expr<'vir> where 'tcx: 'vir;

    type EncodingError = ();

    encoder_cache!(MirBodyPureEncoder);

    fn do_encode_full<'vir, 'tcx>(
        task_key: &Self::TaskKey<'vir, 'tcx>,
        deps: &mut TaskEncoderDependencies<'vir, 'tcx>,
    ) -> Result<(
        Self::OutputFullLocal<'vir, 'tcx>,
        Self::OutputFullDependency<'vir, 'tcx>,
    ), (
        Self::EncodingError,
        Option<Self::OutputFullDependency<'vir, 'tcx>>,
    )> {
        todo!()
    }

    fn task_to_key<'vir, 'tcx>(task: &Self::TaskDescription<'vir, 'tcx>) -> Self::TaskKey<'vir, 'tcx> {
        match task {
            MirBodyPureEncoderTask::Function {
                parent_def_id,
                param_env,
                substs,
            } => (
                parent_def_id.did,
                None,
                substs, // TODO
            ),
            MirBodyPureEncoderTask::Constant {
                parent_def_id,
                promoted,
                param_env,
                substs,
            } => (
                parent_def_id.did,
                Some(*promoted),
                substs, // TODO
            ),
        }
    }

    fn task_to_output_ref<'vir, 'tcx>(_task: &Self::TaskDescription<'vir, 'tcx>) -> Self::OutputRef<'vir, 'tcx> {
        ()
    }
}*/

// delegate to MirBodyPureEncoder
// - MirConstantEncoder
// - MirFunctionPureEncoder
/*
struct MirBodyImpureEncoder<'vir, 'tcx>(PhantomData<&'vir ()>, PhantomData<&'tcx ()>);
impl<'vir, 'tcx> TaskEncoder<'vir, 'tcx> for MirBodyImpureEncoder<'vir, 'tcx> {
    type TaskDescription = (
        ty::WithOptConstParam<DefId>, // ID of the function
        ty::ParamEnv<'tcx>, // param environment at the usage site
        ty::SubstsRef<'tcx>, // type substitutions at the usage site
    );
    // TaskKey, OutputRef same as above
    type OutputFull = vir::Method<'vir>;
} 

struct MirTyEncoder<'vir, 'tcx>(PhantomData<&'vir ()>, PhantomData<&'tcx ()>);
impl<'vir, 'tcx> TaskEncoder<'vir, 'tcx> for MirTyEncoder<'vir, 'tcx> {
    type TaskDescription = ty::Ty<'tcx>;
    // TaskKey = TaskDescription
    type OutputRef = vir::Type<'vir>;
    type OutputFull = (
        Vec<vir::Domain<'vir>>,
        Vec<vir::Predicate<'vir>>,
    );
}
*/

pub fn test_entrypoint<'tcx>(tcx: ty::TyCtxt<'tcx>) {
    use task_encoder::TaskEncoder;

    let vcx = vir::VirCtxt::new(tcx);
    VCTX.replace(Some(unsafe { std::mem::transmute(vcx) }));

    // TODO: this should be a "crate" encoder, which will deps.require all the methods in the crate

    for def_id in tcx.hir_crate_items(()).definitions() {
        //println!("item: {def_id:?}");
        let kind = tcx.def_kind(def_id);
        //println!("  kind: {:?}", kind);
        /*if !format!("{def_id:?}").contains("foo") {
            continue;
        }*/
        match kind {
            hir::def::DefKind::Fn => {
                let res = crate::encoders::MirImpureEncoder::encode(def_id.to_def_id());
                assert!(res.is_ok());
                /*
                match res {
                    Ok(res) => println!("ok: {:?}", res),
                    Err(err) => println!("err: {:?}", err),
                }*/
            }
            unsupported_item_kind => {
                println!("another item: {unsupported_item_kind:?}");
            }
        }
    }
    //println!("all items in crate: {:?}", tcx.hir_crate_items(()).definitions().collect::<Vec<_>>());

    let mut viper_code = String::new();
    for output in crate::encoders::MirImpureEncoder::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.method));
    }
    for output in crate::encoders::MirBuiltinEncoder::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.function));
    }
    for output in crate::encoders::TypeEncoder::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.snapshot));
        for field_projection in &output.field_projection_p {
            viper_code.push_str(&format!("{:?}", field_projection));
        }
        viper_code.push_str(&format!("{:?}\n", output.predicate));
        viper_code.push_str(&format!("{:?}\n", output.method_refold));
    }
    std::fs::write("local-testing/simple.vpr", viper_code);
}
