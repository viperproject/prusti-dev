use crate::{
    debug_info::DebugInfo, viper_ident::ViperIdent, with_vcx, VirCtxt,
};
use crate::data::*;
use crate::refs::*;
use crate::gendata::*;
use crate::genrefs::*;
use sealed::sealed;
use std::{backtrace::Backtrace, fmt::Debug};

pub trait CallableIdent<'vir, A: Arity<'vir>, ResultTy> {
    fn new(name: ViperIdent<'vir>, args: A, result_ty: ResultTy) -> Self;
    fn name(&self) -> ViperIdent<'vir>;
    fn name_str(&self) -> &'vir str {
        self.name().to_str()
    }
    fn arity(&self) -> &A;
    fn result_ty(&self) -> ResultTy;
}
pub trait ToKnownArity<'vir, T: 'vir, ResultTy>: CallableIdent<'vir, UnknownArityAny<'vir, T>, ResultTy> + Sized {
    fn to_known<'tcx, K: CallableIdent<'vir, KnownArityAny<'vir, T, N>, ResultTy>, const N: usize>(self) -> K {
        K::new(
            self.name(),
            KnownArityAny::new(self.arity().args().try_into().unwrap()),
            self.result_ty(),
        )
    }
}
impl<'vir, T: 'vir, ResultTy, K: CallableIdent<'vir, UnknownArityAny<'vir, T>, ResultTy>>
    ToKnownArity<'vir, T, ResultTy> for K
{
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct FunctionIdent<'vir, A: Arity<'vir>>(ViperIdent<'vir>, A, Type<'vir>, DebugInfo<'vir>);

impl<'vir, A: Arity<'vir>> CallableIdent<'vir, A, Type<'vir>> for FunctionIdent<'vir, A> {
    fn new(name: ViperIdent<'vir>, args: A, result_ty: Type<'vir>) -> Self {
        Self(name, args, result_ty, with_vcx(DebugInfo::new))
    }

    fn name(&self) -> ViperIdent<'vir> {
        self.0
    }
    fn arity(&self) -> &A {
        &self.1
    }

    fn result_ty(&self) -> Type<'vir> {
        self.2
    }
}

impl<'vir, A: Arity<'vir, Arg = Type<'vir>>> FunctionIdent<'vir, A> {
    pub fn debug_info(&self) -> DebugInfo<'vir> {
        self.3
    }

    pub fn as_unknown_arity(self) -> FunctionIdent<'vir, UnknownArity<'vir>> {
        FunctionIdent(
            self.name(),
            UnknownArity::new(self.1.args()),
            self.result_ty(),
            self.debug_info(),
        )
    }
}

#[derive(Debug, Clone, Copy)]
pub struct MethodIdent<'vir, A: Arity<'vir>>(ViperIdent<'vir>, A, DebugInfo<'vir>);
impl<'vir, A: Arity<'vir>> CallableIdent<'vir, A, ()> for MethodIdent<'vir, A> {
    fn new(name: ViperIdent<'vir>, args: A, _unused: ()) -> Self {
        Self(name, args, with_vcx(DebugInfo::new))
    }
    fn name(&self) -> ViperIdent<'vir> {
        self.0
    }
    fn arity(&self) -> &A {
        &self.1
    }
    fn result_ty(&self) -> () {
       ()
    }
}

impl <'vir, A: Arity<'vir>> MethodIdent<'vir, A> {
    pub fn debug_info(&self) -> DebugInfo<'vir> {
        self.2
    }
}

impl <'vir, A: Arity<'vir>> MethodIdent<'vir, A> {
    pub fn new(name: ViperIdent<'vir>, args: A) -> Self {
        Self(name, args, with_vcx(DebugInfo::new))
    }
}

impl<'vir, A: Arity<'vir, Arg = Type<'vir>>> MethodIdent<'vir, A> {
    pub fn as_unknown_arity(self) -> MethodIdent<'vir, UnknownArity<'vir>> {
        MethodIdent(self.name(), UnknownArity::new(self.1.args()), self.debug_info())
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct PredicateIdent<'vir, A: Arity<'vir>>(ViperIdent<'vir>, A, DebugInfo<'vir>);
impl<'vir, A: Arity<'vir>> CallableIdent<'vir, A, ()> for PredicateIdent<'vir, A> {
    fn new(name: ViperIdent<'vir>, args: A, _unused: ()) -> Self {
        Self(name, args, with_vcx(DebugInfo::new))
    }
    fn name(&self) -> ViperIdent<'vir> {
        self.0
    }
    fn arity(&self) -> &A {
        &self.1
    }
    fn result_ty(&self) -> () {
        ()
    }
}

impl <'vir, A: Arity<'vir>> PredicateIdent<'vir, A> {
    pub fn debug_info(&self) -> DebugInfo<'vir> {
        self.2
    }
}

impl<'vir, A: Arity<'vir, Arg = Type<'vir>>> PredicateIdent<'vir, A> {
    pub fn new(name: ViperIdent<'vir>, args: A) -> Self {
        Self(name, args, with_vcx(DebugInfo::new))
    }
    pub fn as_unknown_arity(&self) -> PredicateIdent<'vir, UnknownArity<'vir>> {
        PredicateIdent(self.0, UnknownArity::new(self.1.args()), self.debug_info())
    }
}

#[derive(Debug, Clone, Copy)]
pub struct DomainIdent<'vir, A: Arity<'vir>>(ViperIdent<'vir>, A);
impl<'vir, A: Arity<'vir>> CallableIdent<'vir, A, ()> for DomainIdent<'vir, A> {
    fn new(name: ViperIdent<'vir>, args: A, _unused: ()) -> Self {
        Self(name, args)
    }
    fn name(&self) -> ViperIdent<'vir> {
        self.0
    }
    fn arity(&self) -> &A {
        &self.1
    }
    fn result_ty(&self) -> () {
        ()
    }
}

impl<'vir> DomainIdent<'vir, KnownArityAny<'vir, DomainParamData<'vir>, 0>> {
    pub fn nullary(name: ViperIdent<'vir>) -> Self {
        Self(name, KnownArityAny::new(&[]))
    }
}

pub type DomainIdentUnknownArity<'vir> =
    DomainIdent<'vir, UnknownArityAny<'vir, DomainParamData<'vir>>>;

impl<'vir> DomainIdentUnknownArity<'vir> {
    pub fn new(name: ViperIdent<'vir>, args: UnknownArityAny<'vir, DomainParamData<'vir>>) -> Self {
        Self(name, args)
    }
}

#[sealed]
pub trait Arity<'vir>: Copy {
    type Arg;
    fn args(&self) -> &'vir [Self::Arg];

    #[must_use]
    fn len_matches(&self, len: usize) -> bool;
}
#[sealed]
impl<'vir, T, const N: usize> Arity<'vir> for KnownArityAny<'vir, T, N> {
    type Arg = T;
    fn args(&self) -> &'vir [T] {
        &self.0
    }
    fn len_matches(&self, _len: usize) -> bool {
        true
    }
}
#[sealed]
impl<'vir, T> Arity<'vir> for UnknownArityAny<'vir, T> {
    type Arg = T;
    fn args(&self) -> &'vir [T] {
        &self.0
    }

    fn len_matches(&self, len: usize) -> bool {
        self.0.len() == len
    }
}

pub trait HasType<'vir> {
    fn typ(&self) -> Type<'vir>;
}

impl<'vir, Curr, Next> HasType<'vir> for ExprGen<'vir, Curr, Next> {
    fn typ(&self) -> Type<'vir> {
        self.ty()
    }
}

impl<'vir> HasType<'vir> for LocalDecl<'vir> {
    fn typ(&self) -> Type<'vir> {
        self.ty
    }
}

pub trait CheckTypes<'vir> {
    #[must_use]
    fn types_match<T: HasType<'vir>>(&self, args: &[T]) -> bool;
}

impl<'vir, A: Arity<'vir, Arg = Type<'vir>>> CheckTypes<'vir> for A {
    fn types_match<T: HasType<'vir>>(&self, args: &[T]) -> bool {
        if !self.len_matches(args.len()) {
            return false;
        }
        args.iter()
            .zip(self.args().into_iter())
            .all(|(a, expected)| a.typ() == *expected)
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
pub type NullaryArityAny<'vir, T> = KnownArityAny<'vir, T, 0>;

impl<'vir, T, const N: usize> Copy for KnownArityAny<'vir, T, N> {}
pub type KnownArity<'vir, const N: usize> = KnownArityAny<'vir, Type<'vir>, N>;
pub type NullaryArity<'vir> = KnownArity<'vir, 0>;
pub type UnaryArity<'vir> = KnownArity<'vir, 1>;
pub type BinaryArity<'vir> = KnownArity<'vir, 2>;
pub type TernaryArity<'vir> = KnownArity<'vir, 3>;

#[derive(Debug)]
pub struct UnknownArityAny<'vir, T>(&'vir [T]);
impl<'vir, T> UnknownArityAny<'vir, T> {
    pub fn len(&self) -> usize {
        self.0.len()
    }
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
        args: [ExprGen<'vir, Curr, Next>; N],
    ) -> ExprGen<'vir, Curr, Next> {
        self.check_and_apply(vcx, &args)
    }
}

impl<'vir, A: Arity<'vir, Arg = Type<'vir>> + Debug> FunctionIdent<'vir, A> {
    fn check_and_apply<'tcx, Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'tcx>,
        args: &[ExprGen<'vir, Curr, Next>],
    ) -> ExprGen<'vir, Curr, Next> {
        if self.1.types_match(args) {
            vcx.mk_func_app(self.name().to_str(), args, self.result_ty())
        } else {
            panic!(
                "Function {} could not be applied. Expected: {:?}, Actual Exprs: {:?}, Actual Types: {:?}, debug info: {}",
                self.name(),
                self.arity(),
                args,
                args.iter().map(|a| a.ty()).collect::<Vec<_>>(),
                self.debug_info()
            );
        }
    }
}

impl<'vir, A: Arity<'vir, Arg = Type<'vir>> + Debug> PredicateIdent<'vir, A> {
    fn check_and_apply<'tcx, Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'tcx>,
        args: &[ExprGen<'vir, Curr, Next>],
        perm: Option<ExprGen<'vir, Curr, Next>>,
    ) -> PredicateAppGen<'vir, Curr, Next> {
        if self.1.types_match(args) {
            vcx.alloc(PredicateAppGenData {
                target: self.name().to_str(),
                args: vcx.alloc_slice(args),
                perm,
            })
        } else {
            panic!(
                "Predicate {} could not be applied. Expected arg types: {:?}, Actual arg types: {:?}, Debug info: {}",
                self.name(),
                self.arity(),
                args.iter().map(|a| a.ty()).collect::<Vec<_>>(),
                self.debug_info()
            );
        }
    }
}

impl<'vir, const N: usize> PredicateIdent<'vir, KnownArity<'vir, N>> {
    pub fn apply<'tcx, Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'tcx>,
        args: [ExprGen<'vir, Curr, Next>; N],
        perm: Option<ExprGen<'vir, Curr, Next>>,
    ) -> PredicateAppGen<'vir, Curr, Next> {
        self.check_and_apply(vcx, &args, perm)
    }
}
impl<'vir, const N: usize> MethodIdent<'vir, KnownArity<'vir, N>> {
    pub fn apply<'tcx, Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'tcx>,
        args: [ExprGen<'vir, Curr, Next>; N],
    ) -> StmtKindGenData<'vir, Curr, Next> {
        assert!(self.1.types_match(&args));
        StmtKindGenData::MethodCall(vcx.alloc(MethodCallGenData {
            targets: &[],
            method: self.name().to_str(),
            args: vcx.alloc_slice(&args),
        }))
    }
}
impl<'vir, const N: usize> DomainIdent<'vir, KnownArityAny<'vir, DomainParamData<'vir>, N>> {
    pub fn apply<'tcx>(&self, vcx: &'vir VirCtxt<'tcx>, args: [Type<'vir>; N]) -> Type<'vir> {
        vcx.alloc(TypeData::Domain(self.0.to_str(), vcx.alloc_slice(&args)))
    }
}


// Func arity checked at runtime

impl<'vir> FunctionIdent<'vir, UnknownArity<'vir>> {
    pub fn apply<'tcx, Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'tcx>,
        args: &[ExprGen<'vir, Curr, Next>],
    ) -> ExprGen<'vir, Curr, Next> {
        self.check_and_apply(vcx, args)
    }
}

impl<'vir> PredicateIdent<'vir, UnknownArity<'vir>> {
    pub fn apply<'tcx, Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'tcx>,
        args: &[ExprGen<'vir, Curr, Next>],
        perm: Option<ExprGen<'vir, Curr, Next>>,
    ) -> PredicateAppGen<'vir, Curr, Next> {
        self.check_and_apply(vcx, args, perm)
    }
}
impl<'vir> MethodIdent<'vir, UnknownArity<'vir>> {
    pub fn apply<'tcx, Curr: 'vir, Next: 'vir>(
        &self,
        vcx: &'vir VirCtxt<'tcx>,
        args: &[ExprGen<'vir, Curr, Next>],
    ) -> StmtKindGenData<'vir, Curr, Next> {
        if !self.1.types_match(args) {
            panic!(
                "Method {} could not be applied. Expected arg types: {:?}, Actual arg types: {:?}, Debug info: {}",
                self.name(),
                self.arity(),
                args.iter().map(|a| a.ty()).collect::<Vec<_>>(),
                self.debug_info()
            );
        }
        StmtKindGenData::MethodCall(vcx.alloc(MethodCallGenData {
            targets: &[],
            method: self.name().to_str(),
            args: vcx.alloc_slice(args),
        }))
    }
}
impl<'vir> DomainIdent<'vir, UnknownArityAny<'vir, DomainParamData<'vir>>> {
    pub fn apply<'tcx>(&self, vcx: &'vir VirCtxt<'tcx>, args: &[Type<'vir>]) -> Type<'vir> {
        assert!(self.1.len_matches(args.len()));
        vcx.alloc(TypeData::Domain(self.0.to_str(), vcx.alloc_slice(args)))
    }
}
