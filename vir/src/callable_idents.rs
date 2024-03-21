use crate::{VirCtxt, data::*, gendata::*, genrefs::*, refs::*};
use sealed::sealed;
use std::collections::HashMap;

pub trait CallableIdent<'vir, A: Arity<'vir>, ResultTy> {
    fn name(&self) -> &'vir str;
    fn arity(&self) -> &A;
    fn result_ty(&self) -> ResultTy;
}
pub trait ToKnownArity<'vir, T: 'vir, ResultTy>: CallableIdent<'vir, UnknownArityAny<'vir, T>, ResultTy> + Sized {
    type Output<const N: usize>: CallableIdent<'vir, KnownArityAny<'vir, T, N>, ResultTy>;
    fn to_known<const N: usize>(self) -> Self::Output<N>;
}

impl<'vir, T: 'vir> ToKnownArity<'vir, T, Type<'vir>> for FunctionIdent<'vir, UnknownArityAny<'vir, T>> {
    type Output<const N: usize> = FunctionIdent<'vir, KnownArityAny<'vir, T, N>>;
    fn to_known<const N: usize>(self) -> Self::Output<N> {
        FunctionIdent(
            self.name(),
            KnownArityAny::new(self.arity().args().try_into().unwrap()),
            self.result_ty(),
        )
    }
}

#[derive(Debug, Clone, Copy)]
pub struct FunctionIdent<'vir, A: Arity<'vir>>(&'vir str, A, Type<'vir>);
impl<'vir, A: Arity<'vir>> FunctionIdent<'vir, A> {
    pub fn new(name: &'vir str, args: A, result_ty: Type<'vir>) -> Self {
        Self(name, args, result_ty)
    }
}
impl<'vir, A: Arity<'vir>> CallableIdent<'vir, A, Type<'vir>> for FunctionIdent<'vir, A> {
    fn name(&self) -> &'vir str {
        self.0
    }
    fn arity(&self) -> &A {
        &self.1
    }
    fn result_ty(&self) -> Type<'vir> {
        self.2
    }
}

#[derive(Debug, Clone, Copy)]
pub struct MethodIdent<'vir, A: Arity<'vir>>(&'vir str, A);
impl<'vir, A: Arity<'vir>> MethodIdent<'vir, A> {
    pub fn new(name: &'vir str, args: A) -> Self {
        Self(name, args)
    }
}
impl<'vir, A: Arity<'vir>> CallableIdent<'vir, A, ()> for MethodIdent<'vir, A> {
    fn name(&self) -> &'vir str {
        self.0
    }
    fn arity(&self) -> &A {
        &self.1
    }
    fn result_ty(&self) -> () {
       ()
    }
}

#[derive(Debug, Clone, Copy)]
pub struct PredicateIdent<'vir, A: Arity<'vir>>(&'vir str, A);
impl<'vir, A: Arity<'vir>> PredicateIdent<'vir, A> {
    pub fn new(name: &'vir str, args: A) -> Self {
        Self(name, args)
    }
}
impl<'vir, A: Arity<'vir>> CallableIdent<'vir, A, ()> for PredicateIdent<'vir, A> {
    fn name(&self) -> &'vir str {
        self.0
    }
    fn arity(&self) -> &A {
        &self.1
    }
    fn result_ty(&self) -> () {
        ()
    }
}

#[derive(Debug, Clone, Copy)]
pub struct DomainIdent<'vir, A: Arity<'vir>>(&'vir str, A);
impl<'vir, A: Arity<'vir>> DomainIdent<'vir, A> {
    pub fn new(name: &'vir str, args: A) -> Self {
        Self(name, args)
    }
}
impl<'vir, A: Arity<'vir>> CallableIdent<'vir, A, ()> for DomainIdent<'vir, A> {
    fn name(&self) -> &'vir str {
        self.0
    }
    fn arity(&self) -> &A {
        &self.1
    }
    fn result_ty(&self) -> () {
        ()
    }
}
pub type DomainIdentUnknownArity<'vir> = DomainIdent<'vir, UnknownArityAny<'vir, DomainParam<'vir>>>;

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

pub trait CheckTypes<'vir> {
    fn check_types<Curr: 'vir, Next: 'vir>(&self, name: &str, args: &[ExprGen<'vir, Curr, Next>]) -> HashMap<&'vir str, Type<'vir>>;
}

fn unify<'vir>(substs: &mut HashMap<&'vir str, Type<'vir>>, param: &'vir str, ty: Type<'vir>) -> bool {
    match substs.get(param) {
        Some(s) => s == &ty,
        None => substs.insert(param, ty) == None
    }
}

fn check<'vir>(substs: &mut TySubsts<'vir>, expected: Type<'vir>, actual: Type<'vir>) -> bool {
    match (expected, actual) {
        (e, a) if e == a => true,
        (TypeData::Domain(n1, a1), TypeData::Domain(n2, a2)) => {
            n1 == n2 &&
            a1.len() == a2.len() &&
            a1.iter().zip(a2.iter()).all(|(e, a)| check(substs, e, a))
        }
        (TypeData::DomainTypeParam(p), a) => unify(substs, p.name, a),
        _ => false,
    }
}

impl<'vir, A: Arity<'vir, Arg = Type<'vir>>> CheckTypes<'vir> for A {
    fn check_types<Curr: 'vir, Next: 'vir>(&self, name: &str, args: &[ExprGen<'vir, Curr, Next>]) -> TySubsts<'vir> {
        self.check_len_matches(name, args.len());
        let mut substs = TySubsts::new();
        for (arg, expected) in args.iter().zip(self.args().into_iter()) {
            let actual = arg.ty();
            if !check(&mut substs, expected, actual) {
                panic!(
                    "{name} expected arguments {:?} but got argument types {:?}",
                    self.args(),
                    args.iter().map(|a| a.ty()).collect::<Vec<_>>()
                )
            }
        }
        substs
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
        vcx.mk_func_app(self.name(), &args, self.result_ty())
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
impl<'vir, const N: usize> DomainIdent<'vir, KnownArityAny<'vir, DomainParam<'vir>, N>> {
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
        let substs = self.1.check_types(self.name(), args);
        let result_ty = vcx.apply_ty_substs(self.result_ty(), &substs);
        vcx.mk_func_app(self.name(), args, result_ty)
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
impl<'vir> DomainIdent<'vir, UnknownArityAny<'vir, DomainParam<'vir>>> {
    pub fn apply<'tcx>(
        &self,
        vcx: &'vir VirCtxt<'tcx>,
        args: &[Type<'vir>]
    ) -> Type<'vir> {
        self.1.check_len_matches(self.name(), args.len());
        vcx.alloc(TypeData::Domain(self.0, vcx.alloc_slice(args)))
    }
}
