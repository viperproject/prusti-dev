use crate::{
    debug_info::DebugInfo, gendata::*, genrefs::*, refs::*, viper_ident::ViperIdent, with_vcx,
    CastType, CompType, HasType, TypeDyn, VirCtxt,
};
use sealed::sealed;
use serde::{Deserialize, Serialize};
use std::{borrow::Borrow, fmt::Debug, hash::Hash};

/// An empty type that is only used to specify the arity of callable things.
/// Without the `Many` wrapper, exactly one argument of the type is expected,
/// with the wrapper we expect a slice of statically-unknown length.
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
pub struct Many<T: CompType>(core::marker::PhantomData<T>);
macro_rules! typed_wrapper {
    ($wrapper:ident; $($type:ident => $name:ident$(<$($gen:tt),+>)?),+) => {
        $(
            pub type $name$(<$($gen),+>)? = $wrapper<$($($gen,)*)?$crate::$type>;
        )+
    }
}
typed_wrapper!(Many; Bool => ManyBool, Int => ManyInt, Ref => ManyRef, Perm => ManyPerm);
typed_wrapper!(Many; CSnap => ManyCSnap, PSnap => ManyPSnap, TyVal => ManyTyVal);
typed_wrapper!(Many; Prim => ManyPrim, Snap => ManySnap, Dyn => ManyDyn);

// A domain identifier

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(bound(deserialize = "'de: 'vir"))]
pub struct DomainIdn<'vir, R: CompType> {
    idn: ViperIdent<'vir>,
    params: usize,
    _p: core::marker::PhantomData<R>,
}
typed_wrapper!(DomainIdn; CSnap => DomainIdnCSnap<'vir>, PSnap => DomainIdnPSnap<'vir>, TyVal => DomainIdnTyVal<'vir>);
typed_wrapper!(DomainIdn; Prim => DomainIdnPrim<'vir>, Snap => DomainIdnSnap<'vir>, Dyn => DomainIdnDyn<'vir>);

impl<'vir, R: CompType> DomainIdn<'vir, R> {
    pub fn new(idn: ViperIdent<'vir>, params: usize) -> Self {
        let ps = (0..params)
            .map(|_| crate::TypeData::new(crate::TypeKind::Err))
            .collect::<Vec<_>>();
        let ps = ps.iter().collect::<Vec<_>>();
        R::check(&crate::TypeData::<crate::Dyn>::new(
            crate::TypeKind::Domain(idn.to_str(), &ps),
        ));
        Self {
            idn,
            params,
            _p: core::marker::PhantomData,
        }
    }

    pub fn name(&self) -> ViperIdent<'vir> {
        self.idn
    }

    pub fn cast_ty<R1: CompType>(self) -> DomainIdn<'vir, R1> {
        DomainIdn::new(self.idn, self.params)
    }
}

impl<'vir, R: CompType> FnOnce<()> for DomainIdn<'vir, R> {
    type Output = crate::Type<'vir, R>;
    extern "rust-call" fn call_once(self, _args: ()) -> Self::Output {
        with_vcx(|vcx| {
            assert_eq!(self.params, 0);
            let kind = crate::TypeKind::Domain(self.idn.to_str(), &[]);
            vcx.alloc(crate::TypeData::new(kind))
        })
    }
}

impl<'a, 'vir, T: CompType, R: CompType> FnOnce<(&'a [crate::Type<'vir, T>],)>
    for DomainIdn<'vir, R>
{
    type Output = crate::Type<'vir, R>;
    extern "rust-call" fn call_once(self, args: (&'a [crate::Type<'vir, T>],)) -> Self::Output {
        with_vcx(|vcx| {
            assert_eq!(self.params, args.0.len());
            let args = vcx.alloc_slice(args.0);
            let kind = crate::TypeKind::Domain(self.idn.to_str(), args.as_dyn());
            vcx.alloc(crate::TypeData::new(kind))
        })
    }
}

// An Adt destructor

pub struct AdtDestructorWrapper<'vir, T: CompType, R: CompType>(AdtDestructor<'vir, T, R>);

impl<'vir, T: CompType, R: CompType> crate::AdtDestructorData<'vir, T, R> {
    pub fn call(&'vir self) -> AdtDestructorWrapper<'vir, T, R> {
        AdtDestructorWrapper(self)
    }
}

impl<'vir, Curr, Next, T: CompType, R: CompType> FnOnce<(crate::ExprGen<'vir, Curr, Next, T>,)>
    for AdtDestructorWrapper<'vir, T, R>
{
    type Output = crate::ExprGen<'vir, Curr, Next, R>;
    extern "rust-call" fn call_once(
        self,
        args: (crate::ExprGen<'vir, Curr, Next, T>,),
    ) -> Self::Output {
        with_vcx(|vcx| vcx.mk_adt_destructor_expr(args.0, self.0))
    }
}

// Any callable thing

pub trait CallableIdn<'vir, A: Arity> {
    fn name(&self) -> ViperIdent<'vir>;
    fn arity(&self) -> A::Tys<'vir>;
    fn debug_info(&self) -> DebugInfo<'vir>;
    fn cast_args<A1: Arity>(self, args: A1::Tys<'vir>) -> impl CallableIdn<'vir, A1>;
}

// Function Identifier

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FunctionIdn<'vir, A: Arity, R: CompType> {
    idn: ViperIdent<'vir>,
    args: A::Tys<'vir>,
    result_ty: Type<'vir, R>,
    debug_info: DebugInfo<'vir>,
}

impl<'vir, A: Arity, R: CompType> CallableIdn<'vir, A> for FunctionIdn<'vir, A, R> {
    fn name(&self) -> ViperIdent<'vir> {
        self.idn
    }
    fn arity(&self) -> A::Tys<'vir> {
        self.args
    }
    fn debug_info(&self) -> DebugInfo<'vir> {
        self.debug_info
    }
    #[allow(refining_impl_trait)]
    fn cast_args<A1: Arity>(self, args: A1::Tys<'vir>) -> FunctionIdn<'vir, A1, R> {
        A::types_match(self.args, &A1::params(args), self.debug_info);
        FunctionIdn {
            idn: self.idn,
            args,
            result_ty: self.result_ty,
            debug_info: self.debug_info,
        }
    }
}

pub struct FunctionIdnGen<'vir, Curr: 'vir, Next: 'vir, A: Arity, R: CompType> {
    inner: FunctionIdn<'vir, A, R>,
    // TODO: correct variance?
    _p: core::marker::PhantomData<(Curr, Next)>,
}

impl<'vir, A: Arity, R: CompType> FunctionIdn<'vir, A, R> {
    pub fn new(idn: ViperIdent<'vir>, args: A::Tys<'vir>, result_ty: Type<'vir, R>) -> Self {
        Self {
            idn,
            args,
            result_ty,
            debug_info: with_vcx(DebugInfo::new),
        }
    }

    pub fn call<Curr, Next>(self) -> FunctionIdnGen<'vir, Curr, Next, A, R> {
        FunctionIdnGen {
            inner: self,
            _p: core::marker::PhantomData,
        }
    }

    pub fn result(&self) -> Type<'vir, R> {
        self.result_ty
    }

    pub fn cast_ty<A1: Arity, R1: CompType>(
        self,
        args: A1::Tys<'vir>,
    ) -> FunctionIdn<'vir, A1, R1> {
        let self_ = self.cast_args::<A1>(args);
        FunctionIdn {
            idn: self_.idn,
            args: self_.args,
            result_ty: self_.result_ty.inner_cast_ty(),
            debug_info: self_.debug_info,
        }
    }
}

impl<'a, 'vir, A: Arity, R: CompType> FnOnce<A::Exprs<'a, 'vir, (), !>>
    for FunctionIdn<'vir, A, R>
{
    type Output = crate::Expr<'vir, R>;
    extern "rust-call" fn call_once(self, args: A::Exprs<'a, 'vir, (), !>) -> Self::Output {
        self.call().call_once(args)
    }
}

impl<'a, 'vir, Curr: 'vir, Next: 'vir, A: Arity, R: CompType> FnOnce<A::Exprs<'a, 'vir, Curr, Next>>
    for FunctionIdnGen<'vir, Curr, Next, A, R>
{
    type Output = crate::ExprGen<'vir, Curr, Next, R>;
    extern "rust-call" fn call_once(self, args: A::Exprs<'a, 'vir, Curr, Next>) -> Self::Output {
        with_vcx(|vcx| {
            let args = A::args(vcx, args);
            A::types_match(self.inner.args, args, self.inner.debug_info);
            vcx.mk_func_app(self.inner.idn.to_str(), args, self.inner.result_ty, &[])
        })
    }
}

// Method Identifier

#[derive(Debug, Clone, Copy)]
pub struct MethodIdn<'vir, A: Arity> {
    idn: ViperIdent<'vir>,
    args: A::Tys<'vir>,
    debug_info: DebugInfo<'vir>,
}
// pub type MethodIdnAny<'vir> = MethodIdn<'vir, &'vir [crate::TypeDyn<'vir>]>;

impl<'vir, A: Arity> CallableIdn<'vir, A> for MethodIdn<'vir, A> {
    fn name(&self) -> ViperIdent<'vir> {
        self.idn
    }
    fn arity(&self) -> A::Tys<'vir> {
        self.args
    }
    fn debug_info(&self) -> DebugInfo<'vir> {
        self.debug_info
    }
    #[allow(refining_impl_trait)]
    fn cast_args<A1: Arity>(self, args: A1::Tys<'vir>) -> MethodIdn<'vir, A1> {
        A::types_match(self.args, &A1::params(args), self.debug_info);
        MethodIdn {
            idn: self.idn,
            args,
            debug_info: self.debug_info,
        }
    }
}

pub struct MethodIdnGen<'vir, Curr: 'vir, Next: 'vir, A: Arity> {
    inner: MethodIdn<'vir, A>,
    _p: core::marker::PhantomData<(Curr, Next)>,
}

impl<'vir, A: Arity> MethodIdn<'vir, A> {
    pub fn new(idn: ViperIdent<'vir>, args: A::Tys<'vir>) -> Self {
        Self {
            idn,
            args,
            debug_info: with_vcx(DebugInfo::new),
        }
    }

    pub fn call<Curr, Next>(self) -> MethodIdnGen<'vir, Curr, Next, A> {
        MethodIdnGen {
            inner: self,
            _p: core::marker::PhantomData,
        }
    }
}
impl<'a, 'vir, A: Arity> FnOnce<A::Exprs<'a, 'vir, (), !>> for MethodIdn<'vir, A> {
    type Output = StmtKindGenData<'vir, (), !>;
    extern "rust-call" fn call_once(self, args: A::Exprs<'a, 'vir, (), !>) -> Self::Output {
        self.call().call_once(args)
    }
}
impl<'a, 'vir, Curr: 'vir, Next: 'vir, A: Arity> FnOnce<A::Exprs<'a, 'vir, Curr, Next>>
    for MethodIdnGen<'vir, Curr, Next, A>
{
    type Output = StmtKindGenData<'vir, Curr, Next>;
    extern "rust-call" fn call_once(self, args: A::Exprs<'a, 'vir, Curr, Next>) -> Self::Output {
        with_vcx(|vcx| {
            let args = A::args(vcx, args);
            A::types_match(self.inner.args, args, self.inner.debug_info);
            StmtKindGenData::MethodCall(vcx.alloc(MethodCallGenData {
                targets: &[],
                method: self.inner.idn.to_str(),
                args,
            }))
        })
    }
}

// Predicate Identifier

#[derive(Debug, Clone, Copy)]
pub struct PredicateIdn<'vir, A: Arity> {
    idn: ViperIdent<'vir>,
    args: A::Tys<'vir>,
    debug_info: DebugInfo<'vir>,
}
// pub type PredicateIdnAny<'vir> = PredicateIdn<'vir, &'vir [crate::TypeDyn<'vir>]>;

impl<'vir, A: Arity> CallableIdn<'vir, A> for PredicateIdn<'vir, A> {
    fn name(&self) -> ViperIdent<'vir> {
        self.idn
    }
    fn arity(&self) -> A::Tys<'vir> {
        self.args
    }
    fn debug_info(&self) -> DebugInfo<'vir> {
        self.debug_info
    }
    #[allow(refining_impl_trait)]
    fn cast_args<A1: Arity>(self, args: A1::Tys<'vir>) -> PredicateIdn<'vir, A1> {
        A::types_match(self.args, &A1::params(args), self.debug_info);
        PredicateIdn {
            idn: self.idn,
            args,
            debug_info: self.debug_info,
        }
    }
}

type VarianceBound<'a, Curr, Next> = core::marker::PhantomData<(Box<dyn Fn(&'a ())>, Curr, Next)>;

pub struct PredicateIdnGen<'a, 'vir, Curr: 'vir, Next: 'vir, A: Arity> {
    inner: PredicateIdn<'vir, A>,
    _p: VarianceBound<'a, Curr, Next>,
}

impl<'vir, A: Arity> PredicateIdn<'vir, A> {
    pub fn new(idn: ViperIdent<'vir>, args: A::Tys<'vir>) -> Self {
        Self {
            idn,
            args,
            debug_info: with_vcx(DebugInfo::new),
        }
    }

    pub fn call_once<'a, Curr, Next>(
        self,
        args: A::Exprs<'a, 'vir, Curr, Next>,
    ) -> PredicateIdnCurry<'vir, Curr, Next> {
        self.call().call_once(args)
    }

    pub fn call<'a, Curr, Next>(self) -> PredicateIdnGen<'a, 'vir, Curr, Next, A> {
        PredicateIdnGen {
            inner: self,
            _p: core::marker::PhantomData,
        }
    }
}

impl<'a, 'vir, A: Arity> FnOnce<A::Exprs<'a, 'vir, (), !>> for PredicateIdn<'vir, A> {
    type Output = PredicateIdnCurry<'vir, (), !>;
    extern "rust-call" fn call_once(self, args: A::Exprs<'a, 'vir, (), !>) -> Self::Output {
        self.call().call_once(args)
    }
}

impl<'a, 'vir, Curr: 'vir, Next: 'vir, A: Arity> FnOnce<A::Exprs<'a, 'vir, Curr, Next>>
    for PredicateIdnGen<'a, 'vir, Curr, Next, A>
{
    type Output = PredicateIdnCurry<'vir, Curr, Next>;
    extern "rust-call" fn call_once(self, args: A::Exprs<'a, 'vir, Curr, Next>) -> Self::Output {
        let args = with_vcx(|vcx| A::args(vcx, args));
        A::types_match(self.inner.args, args, self.inner.debug_info);
        PredicateIdnCurry {
            target: self.inner.idn.to_str(),
            args,
        }
    }
}

#[derive(Clone, Copy)]
pub struct PredicateIdnCurry<'vir, Curr: 'vir, Next: 'vir> {
    target: &'vir str,
    args: &'vir [ExprGenDyn<'vir, Curr, Next>],
}

impl<'vir, Curr: 'vir, Next: 'vir> FnOnce<(Option<ExprGenPerm<'vir, Curr, Next>>,)>
    for PredicateIdnCurry<'vir, Curr, Next>
{
    type Output = PredicateAppGen<'vir, Curr, Next>;
    extern "rust-call" fn call_once(
        self,
        args: (Option<ExprGenPerm<'vir, Curr, Next>>,),
    ) -> Self::Output {
        with_vcx(|vcx| {
            vcx.alloc(PredicateAppGenData {
                target: self.target,
                args: self.args,
                perm: args.0,
            })
        })
    }
}

// Field

impl<'vir, Curr: 'vir, Next: 'vir, T: CompType> FnOnce<(ExprGenRef<'vir, Curr, Next>,)>
    for Field<'vir, T>
{
    type Output = ExprGen<'vir, Curr, Next, T>;
    extern "rust-call" fn call_once(self, args: (ExprGenRef<'vir, Curr, Next>,)) -> Self::Output {
        with_vcx(|vcx| vcx.mk_field_expr(args.0, self))
    }
}

// Arity

pub trait Arg:
    'static
    + Clone
    + Copy
    + core::fmt::Debug
    + PartialEq
    + Eq
    + PartialOrd
    + Ord
    + Hash
    + Serialize
    + for<'de> Deserialize<'de>
{
    /// The argument type that this must be called with. Either a single expr
    /// with a known type (e.g. `ExprSnap`) or a slice of exprs with the same
    /// type (e.g. `&'a [ExprDyn]`).
    type Expr<'a, 'vir: 'a, Curr: 'vir, Next: 'vir>;
    type Local<'a, 'vir: 'a>;
    type Ty<'vir>: Copy + Debug;
    type T: CompType;
    fn args<'a, 'vir: 'a, Curr: 'vir, Next: 'vir>(
        args: Self::Expr<'a, 'vir, Curr, Next>,
    ) -> impl Borrow<[ExprGen<'vir, Curr, Next, Self::T>]>;
    fn locals<'a, 'vir: 'a>(
        locals: Self::Local<'a, 'vir>,
    ) -> impl Borrow<[LocalDecl<'vir, Self::T>]>;
    fn params<'a, 'vir>(param: &'a Self::Ty<'vir>) -> &'a [Type<'vir, Self::T>];
}

impl<T: CompType> Arg for T {
    type Expr<'a, 'vir: 'a, Curr: 'vir, Next: 'vir> = ExprGen<'vir, Curr, Next, T>;
    type Local<'a, 'vir: 'a> = LocalDecl<'vir, T>;
    type Ty<'vir> = Type<'vir, T>;
    type T = T;

    fn args<'a, 'vir: 'a, Curr: 'vir, Next: 'vir>(
        args: Self::Expr<'a, 'vir, Curr, Next>,
    ) -> impl Borrow<[ExprGen<'vir, Curr, Next, Self::T>]> {
        [args]
    }
    fn locals<'a, 'vir: 'a>(
        locals: Self::Local<'a, 'vir>,
    ) -> impl Borrow<[LocalDecl<'vir, Self::T>]> {
        [locals]
    }
    fn params<'a, 'vir>(param: &'a Self::Ty<'vir>) -> &'a [Type<'vir, Self::T>] {
        core::slice::from_ref(param)
    }
}

// Unfortunately we cannot implement this for `[T]` because rustc will complain
// about the type `([T], ...)` where an `?Sized` is not the last element of the
// tuple (we cannot implement `Arity` for this tuple).
impl<T: CompType> Arg for Many<T> {
    type Expr<'a, 'vir: 'a, Curr: 'vir, Next: 'vir> = &'a [ExprGen<'vir, Curr, Next, T>];
    type Local<'a, 'vir: 'a> = &'a [LocalDecl<'vir, T>];
    type Ty<'vir> = &'vir [Type<'vir, T>];
    type T = T;
    fn args<'a, 'vir: 'a, Curr: 'vir, Next: 'vir>(
        args: Self::Expr<'a, 'vir, Curr, Next>,
    ) -> impl Borrow<[ExprGen<'vir, Curr, Next, Self::T>]> {
        args
    }
    fn locals<'a, 'vir: 'a>(
        locals: Self::Local<'a, 'vir>,
    ) -> impl Borrow<[LocalDecl<'vir, Self::T>]> {
        locals
    }
    fn params<'a, 'vir>(param: &'a Self::Ty<'vir>) -> &'vir [Type<'vir, Self::T>] {
        param
    }
}

/// Something that indicates the arity and type of arguments. Implemented for
/// tuples of size 0 to 12, where each element is an `Arg`. An `Arg` is either
/// the exact type of the argument (e.g. `TypePerm<'vir>` = `T<'vir, Perm>`) or
/// a slice of an unknown number of arguments of the same type (e.g.
/// `&[TypeSnap<'vir>]` or `&[TypeDyn<'vir>]`).
///
/// This means that a `FunctionIdn<'vir, (TypeSnap<'vir>, &[TypeTyVal<'vir>],
/// TypePerm<'vir>), TypeInt<'vir>>` must be called with `(ExprSnap<'vir>,
/// &[ExprTyVal<'vir>], ExprPerm<'vir>)` and produces an `ExprInt<'vir>`.
#[sealed]
pub trait Arity:
    'static
    + Clone
    + Copy
    + core::fmt::Debug
    + PartialEq
    + Eq
    + PartialOrd
    + Ord
    + Hash
    + Serialize
    + for<'de> Deserialize<'de>
{
    /// The arguments that this will be called with, must be a tuple. For
    /// example `(ExprSnap, &'a [ExprTyVal], ExprPerm)`.
    type Exprs<'a, 'vir: 'a, Curr: 'vir, Next: 'vir>: core::marker::Tuple;
    type Locals<'a, 'vir: 'a>: core::marker::Tuple;
    type Tys<'vir>: Copy + Debug;

    /// Check that the arguments are of the correct type.
    fn types_match<'vir, T: CompType, E: HasType<'vir, T>>(
        params: Self::Tys<'vir>,
        args: &[&'vir E],
        debug_info: DebugInfo<'vir>,
    ) {
        let params = Self::params(params);
        if params.len() != args.len() {
            crate::typecheck_error!(
                "Expected {} arguments, got {}, Debug info: {debug_info}",
                params.len(),
                args.len()
            );
        }
        for (i, (param, arg)) in params.iter().zip(args).enumerate() {
            if param.kind() != arg.ty().kind() {
                crate::typecheck_error!(
                    "Argument {i} has type {:?}, expected {:?}, Debug info: {debug_info}",
                    arg.ty().ty(),
                    param,
                );
            }
        }
    }

    /// Convert the arguments to usable slice.
    fn args<'a, 'vir: 'a, Curr: 'vir, Next: 'vir>(
        vcx: &'vir VirCtxt,
        args: Self::Exprs<'a, 'vir, Curr, Next>,
    ) -> &'vir [ExprGenDyn<'vir, Curr, Next>];

    fn locals<'a, 'vir: 'a>(
        vcx: &'vir VirCtxt,
        locals: Self::Locals<'a, 'vir>,
    ) -> &'vir [LocalDeclDyn<'vir>];

    fn params<'vir>(params: Self::Tys<'vir>) -> Vec<TypeDyn<'vir>>;
}

// pub trait KnownArity<'vir>: Arity<'vir> {
//     /// The number of arguments that this will be called with.
//     const ARITY: usize;
//     fn from_unknown<T: CompType>(tys: &[T<'vir, T>]) -> Self;
// }

macro_rules! tuple_arity {
    ($($g:ident),*) => {
        #[sealed]
        impl<$($g: Arg),*> Arity for ($($g),*) {
            type Exprs<'a, 'vir: 'a, Curr: 'vir, Next: 'vir> = ($($g::Expr<'a, 'vir, Curr, Next>),*);
            type Locals<'a, 'vir: 'a> = ($($g::Local<'a, 'vir>),*);
            type Tys<'vir> = ($($g::Ty<'vir>),*);
            #[allow(unused_variables)]
            fn args<'a, 'vir: 'a, Curr: 'vir, Next: 'vir>(vcx: &'vir VirCtxt, args: Self::Exprs<'a, 'vir, Curr, Next>) -> &'vir [ExprGenDyn<'vir, Curr, Next>] {
                let a = core::iter::empty();
                $(
                    let t = $g::args(args.${index()});
                    let a = a.chain(t.borrow().as_dyn().iter().copied());
                )*
                vcx.alloc_slice(&a.collect::<Vec<_>>())
            }
            #[allow(unused_variables)]
            fn locals<'a, 'vir: 'a>(vcx: &'vir VirCtxt, locals: Self::Locals<'a, 'vir>) -> &'vir [LocalDeclDyn<'vir>] {
                let a = core::iter::empty();
                $(
                    let t = $g::locals(locals.${index()});
                    let a = a.chain(t.borrow().as_dyn().iter().copied());
                )*
                vcx.alloc_slice(&a.collect::<Vec<_>>())
            }
            fn params<'vir>(params: Self::Tys<'vir>) -> Vec<TypeDyn<'vir>> {
                [$($g::params(&params.${index()}).as_dyn()),*]
                    .into_iter()
                    .flatten()
                    .copied()
                    .collect()
            }
        }
    };
}
macro_rules! tuple_arity_many {
    ($f:ident, $g:ident) => {
        tuple_arity!($f, $g);
    };
    ($f:ident $(, $g:ident)*) => {
        tuple_arity!($f $(, $g)*);
        tuple_arity_many!($($g),*);
    }
}
tuple_arity_many!(A, B, C, D, E, F, G, H, I, J, K, L);

#[sealed]
impl<T: Arg> Arity for T {
    type Exprs<'a, 'vir: 'a, Curr: 'vir, Next: 'vir> = (T::Expr<'a, 'vir, Curr, Next>,);
    type Locals<'a, 'vir: 'a> = (T::Local<'a, 'vir>,);
    type Tys<'vir> = T::Ty<'vir>;

    fn args<'a, 'vir: 'a, Curr: 'vir, Next: 'vir>(
        vcx: &'vir VirCtxt,
        args: Self::Exprs<'a, 'vir, Curr, Next>,
    ) -> &'vir [ExprGenDyn<'vir, Curr, Next>] {
        let t = T::args(args.0);
        vcx.alloc_slice(t.borrow().as_dyn())
    }
    fn locals<'a, 'vir: 'a>(
        vcx: &'vir VirCtxt,
        locals: Self::Locals<'a, 'vir>,
    ) -> &'vir [LocalDeclDyn<'vir>] {
        let t = T::locals(locals.0);
        vcx.alloc_slice(t.borrow().as_dyn())
    }
    fn params<'vir>(params: Self::Tys<'vir>) -> Vec<TypeDyn<'vir>> {
        <T as Arg>::params(&params).as_dyn().to_vec()
    }
}

#[sealed]
impl Arity for () {
    type Exprs<'a, 'vir: 'a, Curr: 'vir, Next: 'vir> = ();
    type Locals<'a, 'vir: 'a> = ();
    type Tys<'vir> = ();

    fn args<'a, 'vir: 'a, Curr: 'vir, Next: 'vir>(
        _vcx: &'vir VirCtxt,
        _args: Self::Exprs<'a, 'vir, Curr, Next>,
    ) -> &'vir [ExprGenDyn<'vir, Curr, Next>] {
        &[]
    }
    fn locals<'a, 'vir: 'a>(
        _vcx: &'vir VirCtxt,
        _locals: Self::Locals<'a, 'vir>,
    ) -> &'vir [LocalDeclDyn<'vir>] {
        &[]
    }
    fn params<'vir>(_params: Self::Tys<'vir>) -> Vec<TypeDyn<'vir>> {
        Vec::new()
    }
}

// pub trait Args<'vir>: Borrow<[Type<'vir>]> {
//     fn alloc(&self, vcx: &'vir VirCtxt) -> &'vir [Type<'vir>];
// }

// impl<'vir, const N: usize> Args<'vir> for [Type<'vir>; N] {
//     fn alloc(&self, vcx: &'vir VirCtxt) -> &'vir [Type<'vir>] {
//         vcx.alloc_array(self)
//     }
// }

// impl<'vir> Args<'vir> for &'vir [Type<'vir>] {
//     fn alloc(&self, _vcx: &'vir VirCtxt) -> &'vir [Type<'vir>] {
//         self
//     }
// }

#[test]
fn test_arity() {
    use crate::*;
    crate::init_vcx(crate::VirCtxt::new_without_tcx());
    let ints = &[TYPE_INT, TYPE_INT][..];
    let a = (ints, TYPE_BOOL);
    let f_idn = FunctionIdn::<(ManyInt, Bool), Ref>::new(ViperIdent::new("foo"), a, TYPE_REF);
    let i = &ExprData::new(&ExprKindData::Const(&ConstData::Int(0)));
    let j = &ExprData::new(&ExprKindData::Const(&ConstData::Bool(true)));
    let _d = f_idn(&[i, i], j);
}
