use crate::{ExprGen, PredicateAppGen, Type, PredicateAppGenData, StmtGenData, MethodCallGenData, VirCtxt};
use sealed::sealed;

pub trait CallableIdent<'vir, A: Arity> {
    fn new(name: &'vir str, args: A) -> Self;
    fn name(&self) -> &'vir str;
    fn arity(&self) -> A;
}

#[derive(Debug, Clone, Copy)]
pub struct FunctionIdent<'vir, A: Arity>(&'vir str, A);
impl<'vir, A: Arity> CallableIdent<'vir, A> for FunctionIdent<'vir, A> {
    fn new(name: &'vir str, args: A) -> Self {
        Self(name, args)
    }
    fn name(&self) -> &'vir str {
        self.0
    }
    fn arity(&self) -> A {
        self.1
    }
}

#[derive(Debug, Clone, Copy)]
pub struct MethodIdent<'vir, A: Arity>(&'vir str, A);
impl<'vir, A: Arity> CallableIdent<'vir, A> for MethodIdent<'vir, A> {
    fn new(name: &'vir str, args: A) -> Self {
        Self(name, args)
    }
    fn name(&self) -> &'vir str {
        self.0
    }
    fn arity(&self) -> A {
        self.1
    }
}

#[derive(Debug, Clone, Copy)]
pub struct PredicateIdent<'vir, A: Arity>(&'vir str, A);
impl<'vir, A: Arity> CallableIdent<'vir, A> for PredicateIdent<'vir, A> {
    fn new(name: &'vir str, args: A) -> Self {
        Self(name, args)
    }
    fn name(&self) -> &'vir str {
        self.0
    }
    fn arity(&self) -> A {
        self.1
    }
}

#[sealed]
pub trait Arity: Copy {
    fn args(&self) -> &[Type];
    fn len_matches(&self, len: usize) -> bool;
    fn check<'vir, Curr: 'vir, Next: 'vir>(&self, name: &str, args: &[ExprGen<'vir, Curr, Next>]) {
        if cfg!(debug_assertions) {
            let args_len = args.len();
            assert!(self.len_matches(args_len), "{name} called with {args_len} args (expected {})", self.args().len());
            for (_arg, _ty) in args.iter().zip(self.args()) {
                // TODO: check that the types match
            }
        }
        // TODO: return result type
    }
}
#[sealed]
impl<const N: usize> Arity for KnownArity<'_, N> {
    fn args(&self) -> &[Type] {
        &self.0
    }
    fn len_matches(&self, _len: usize) -> bool {
        true
    }
}
#[sealed]
impl Arity for UnknownArity<'_> {
    fn args(&self) -> &[Type] {
        self.0
    }
    fn len_matches(&self, len: usize) -> bool {
        self.0.len() == len
    }
}

#[derive(Debug, Clone, Copy)]
pub struct KnownArity<'vir, const N: usize>([Type<'vir>; N]);
impl<'vir, const N: usize> KnownArity<'vir, N> {
    pub const fn new(types: [Type<'vir>; N]) -> Self {
        Self(types)
    }
}
pub type NullaryArity = KnownArity<'static, 0>;
pub type UnaryArity<'vir> = KnownArity<'vir, 1>;
pub type BinaryArity<'vir> = KnownArity<'vir, 2>;

#[derive(Debug, Clone, Copy)]
pub struct UnknownArity<'vir>(&'vir [Type<'vir>]);
impl<'vir> UnknownArity<'vir> {
    pub const fn new(types: &'vir [Type<'vir>]) -> Self {
        Self(types)
    }
}

// Func arity known at compile time

impl<'vir, const N: usize> FunctionIdent<'vir, KnownArity<'vir, N>> {
    pub fn apply<Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'vir>,
        args: [ExprGen<'vir, Curr, Next>; N]
    ) -> ExprGen<'vir, Curr, Next>{
        self.1.check(self.name(), &args);
        vcx.mk_func_app(self.name(), &args)
    }
}
impl<'vir, const N: usize> PredicateIdent<'vir, KnownArity<'vir, N>> {
    pub fn apply<Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'vir>,
        args: [ExprGen<'vir, Curr, Next>; N]
    ) -> PredicateAppGen<'vir, Curr, Next>{
        self.1.check(self.name(), &args);
        vcx.alloc(PredicateAppGenData {
            target: self.name(),
            args: vcx.alloc_slice(&args),
        })
    }
}
impl<'vir, const N: usize> MethodIdent<'vir, KnownArity<'vir, N>> {
    pub fn apply<Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'vir>,
        args: [ExprGen<'vir, Curr, Next>; N]
    ) -> StmtGenData<'vir, Curr, Next>{
        self.1.check(self.name(), &args);
        StmtGenData::MethodCall(vcx.alloc(MethodCallGenData {
            targets: &[],
            method: self.name(),
            args: vcx.alloc_slice(&args),
        }))
    }
}

// Func arity checked at runtime

impl<'vir> FunctionIdent<'vir, UnknownArity<'vir>> {
    pub fn apply<Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'vir>,
        args: &[ExprGen<'vir, Curr, Next>]
    ) -> ExprGen<'vir, Curr, Next>{
        self.1.check(self.name(), args);
        vcx.mk_func_app(self.name(), args)
    }
}
impl<'vir> PredicateIdent<'vir, UnknownArity<'vir>> {
    pub fn apply<Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'vir>,
        args: &[ExprGen<'vir, Curr, Next>]
    ) -> PredicateAppGen<'vir, Curr, Next>{
        self.1.check(self.name(), args);
        vcx.alloc(PredicateAppGenData {
            target: self.name(),
            args: vcx.alloc_slice(args),
        })
    }
}
impl<'vir> MethodIdent<'vir, UnknownArity<'vir>> {
    pub fn apply<Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'vir>,
        args: &[ExprGen<'vir, Curr, Next>]
    ) -> StmtGenData<'vir, Curr, Next>{
        self.1.check(self.name(), args);
        StmtGenData::MethodCall(vcx.alloc(MethodCallGenData {
            targets: &[],
            method: self.name(),
            args: vcx.alloc_slice(args),
        }))
    }
}
