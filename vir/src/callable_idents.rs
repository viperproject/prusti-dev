use crate::{ExprGen, PredicateAppGen, Type, PredicateAppGenData, StmtGenData, MethodCallGenData, VirCtxt, TypeData, DomainParamData};
use sealed::sealed;

pub trait CallableIdent<'vir, A: Arity<'vir>> {
    fn new(name: &'vir str, args: A) -> Self;
    fn name(&self) -> &'vir str;
    fn arity(&self) -> &A;
}
pub trait ToKnownArity<'vir, T: 'vir>: CallableIdent<'vir, UnknownArityAny<'vir, T>> + Sized {
    fn to_known<'tcx, K: CallableIdent<'vir, KnownArityAny<'vir, T, N>>, const N: usize>(self) -> K {
        K::new(self.name(), KnownArityAny::new(self.arity().args().try_into().unwrap()))
    }
}
impl<'vir, T: 'vir, K: CallableIdent<'vir, UnknownArityAny<'vir, T>>> ToKnownArity<'vir, T> for K {}

#[derive(Debug, Clone, Copy)]
pub struct FunctionIdent<'vir, A: Arity<'vir>>(&'vir str, A);
impl<'vir, A: Arity<'vir>> CallableIdent<'vir, A> for FunctionIdent<'vir, A> {
    fn new(name: &'vir str, args: A) -> Self {
        Self(name, args)
    }
    fn name(&self) -> &'vir str {
        self.0
    }
    fn arity(&self) -> &A {
        &self.1
    }
}

#[derive(Debug, Clone, Copy)]
pub struct MethodIdent<'vir, A: Arity<'vir>>(&'vir str, A);
impl<'vir, A: Arity<'vir>> CallableIdent<'vir, A> for MethodIdent<'vir, A> {
    fn new(name: &'vir str, args: A) -> Self {
        Self(name, args)
    }
    fn name(&self) -> &'vir str {
        self.0
    }
    fn arity(&self) -> &A {
        &self.1
    }
}

#[derive(Debug, Clone, Copy)]
pub struct PredicateIdent<'vir, A: Arity<'vir>>(&'vir str, A);
impl<'vir, A: Arity<'vir>> CallableIdent<'vir, A> for PredicateIdent<'vir, A> {
    fn new(name: &'vir str, args: A) -> Self {
        Self(name, args)
    }
    fn name(&self) -> &'vir str {
        self.0
    }
    fn arity(&self) -> &A {
        &self.1
    }
}

#[derive(Debug, Clone, Copy)]
pub struct DomainIdent<'vir, A: Arity<'vir>>(&'vir str, A);
impl<'vir, A: Arity<'vir>> CallableIdent<'vir, A> for DomainIdent<'vir, A> {
    fn new(name: &'vir str, args: A) -> Self {
        Self(name, args)
    }
    fn name(&self) -> &'vir str {
        self.0
    }
    fn arity(&self) -> &A {
        &self.1
    }
}
pub type DomainIdentUnknownArity<'vir> = DomainIdent<'vir, UnknownArityAny<'vir, DomainParamData<'vir>>>;

#[sealed]
pub trait Arity<'vir>: Copy {
    type Arg;
    fn args(&self) -> &'vir [Self::Arg];
    fn check_len_matches(&self, name: &str, len: usize);
}
#[sealed]
impl<'vir, T, const N: usize> Arity<'vir> for KnownArityAny<'vir, T, N> {
    type Arg = T;
    fn args(&self) -> &'vir [T] {
        &self.0
    }
    fn check_len_matches(&self, _name: &str, _len: usize) {}
}
#[sealed]
impl<'vir, T> Arity<'vir> for UnknownArityAny<'vir, T> {
    type Arg = T;
    fn args(&self) -> &'vir [T] {
        &self.0
    }
    fn check_len_matches(&self, name: &str, len: usize) {
        assert_eq!(self.0.len(), len, "{name} called with {len} args (expected {})", self.0.len());
    }
}

trait CheckTypes<'vir> {
    fn check_types<Curr: 'vir, Next: 'vir>(&self, name: &str, args: &[ExprGen<'vir, Curr, Next>]);
}
impl<'vir, A: Arity<'vir, Arg = Type<'vir>>> CheckTypes<'vir> for A {
    fn check_types<Curr: 'vir, Next: 'vir>(&self, name: &str, args: &[ExprGen<'vir, Curr, Next>]) {
        if cfg!(debug_assertions) {
            self.check_len_matches(name, args.len());
            for (_arg, _ty) in args.iter().zip(self.args().into_iter()) {
                // TODO: check that the types match
            }
        }
        // TODO: return result type
    }
}

#[derive(Debug)]
pub struct KnownArityAny<'vir, T, const N: usize>(&'vir [T]);
impl<'vir, T, const N: usize> KnownArityAny<'vir, T, N> {
    pub const fn new(types: &'vir [T; N]) -> Self {
        Self(types)
    }
}
impl<'vir, T, const N: usize> Clone for KnownArityAny<'vir, T, N> {
    fn clone(&self) -> Self {
        Self(self.0)
    }
}
impl<'vir, T, const N: usize> Copy for KnownArityAny<'vir, T, N> {}
pub type KnownArity<'vir, const N: usize> = KnownArityAny<'vir, Type<'vir>, N>;
pub type NullaryArity<'vir> = KnownArity<'vir, 0>;
pub type UnaryArity<'vir> = KnownArity<'vir, 1>;
pub type BinaryArity<'vir> = KnownArity<'vir, 2>;

#[derive(Debug)]
pub struct UnknownArityAny<'vir, T>(&'vir [T]);
impl<'vir, T> UnknownArityAny<'vir, T> {
    pub const fn new(types: &'vir [T]) -> Self {
        Self(types)
    }
}
impl<'vir, T> Clone for UnknownArityAny<'vir, T> {
    fn clone(&self) -> Self {
        Self(self.0)
    }
}
impl<'vir, T> Copy for UnknownArityAny<'vir, T> {}
pub type UnknownArity<'vir> = UnknownArityAny<'vir, Type<'vir>>;

// Func arity known at compile time
// TODO: maybe take `args: &[T; N]` instead?

impl<'vir, const N: usize> FunctionIdent<'vir, KnownArity<'vir, N>> {
    pub fn apply<'tcx, Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'tcx>,
        args: [ExprGen<'vir, Curr, Next>; N]
    ) -> ExprGen<'vir, Curr, Next>{
        self.1.check_types(self.name(), &args);
        vcx.mk_func_app(self.name(), &args, None)
    }
}
impl<'vir, const N: usize> PredicateIdent<'vir, KnownArity<'vir, N>> {
    pub fn apply<'tcx, Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'tcx>,
        args: [ExprGen<'vir, Curr, Next>; N],
        perm: Option<ExprGen<'vir, Curr, Next>>,
    ) -> PredicateAppGen<'vir, Curr, Next>{
        self.1.check_types(self.name(), &args);
        vcx.alloc(PredicateAppGenData {
            target: self.name(),
            args: vcx.alloc_slice(&args),
            perm,
        })
    }
}
impl<'vir, const N: usize> MethodIdent<'vir, KnownArity<'vir, N>> {
    pub fn apply<'tcx, Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'tcx>,
        args: [ExprGen<'vir, Curr, Next>; N]
    ) -> StmtGenData<'vir, Curr, Next>{
        self.1.check_types(self.name(), &args);
        StmtGenData::MethodCall(vcx.alloc(MethodCallGenData {
            targets: &[],
            method: self.name(),
            args: vcx.alloc_slice(&args),
        }))
    }
}
impl<'vir, const N: usize> DomainIdent<'vir, KnownArityAny<'vir, DomainParamData<'vir>, N>> {
    pub fn apply<'tcx>(
        &self,
        vcx: &'vir VirCtxt<'tcx>,
        args: [Type<'vir>; N]
    ) -> Type<'vir>{
        self.1.check_len_matches(self.name(), args.len());
        vcx.alloc(TypeData::Domain(self.0, vcx.alloc_slice(&args)))
    }
}

// Func arity checked at runtime

impl<'vir> FunctionIdent<'vir, UnknownArity<'vir>> {
    pub fn apply<'tcx, Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'tcx>,
        args: &[ExprGen<'vir, Curr, Next>]
    ) -> ExprGen<'vir, Curr, Next>{
        self.1.check_types(self.name(), args);
        vcx.mk_func_app(self.name(), args, None)
    }
    // TODO: deduplicate
    pub fn apply_ty<'tcx, Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'tcx>,
        args: &[ExprGen<'vir, Curr, Next>],
        result_ty: Type<'vir>
    ) -> ExprGen<'vir, Curr, Next>{
        self.1.check_types(self.name(), args);
        vcx.mk_func_app(self.name(), args, Some(result_ty))
    }
}
impl<'vir> PredicateIdent<'vir, UnknownArity<'vir>> {
    pub fn apply<'tcx, Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'tcx>,
        args: &[ExprGen<'vir, Curr, Next>],
        perm: Option<ExprGen<'vir, Curr, Next>>,
    ) -> PredicateAppGen<'vir, Curr, Next>{
        self.1.check_types(self.name(), args);
        vcx.alloc(PredicateAppGenData {
            target: self.name(),
            args: vcx.alloc_slice(args),
            perm,
        })
    }
}
impl<'vir> MethodIdent<'vir, UnknownArity<'vir>> {
    pub fn apply<'tcx, Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'tcx>,
        args: &[ExprGen<'vir, Curr, Next>]
    ) -> StmtGenData<'vir, Curr, Next>{
        self.1.check_types(self.name(), args);
        StmtGenData::MethodCall(vcx.alloc(MethodCallGenData {
            targets: &[],
            method: self.name(),
            args: vcx.alloc_slice(args),
        }))
    }
}
impl<'vir> DomainIdent<'vir, UnknownArityAny<'vir, DomainParamData<'vir>>> {
    pub fn apply<'tcx>(
        &self,
        vcx: &'vir VirCtxt<'tcx>,
        args: &[Type<'vir>]
    ) -> Type<'vir> {
        self.1.check_len_matches(self.name(), args.len());
        vcx.alloc(TypeData::Domain(self.0, vcx.alloc_slice(args)))
    }
}
