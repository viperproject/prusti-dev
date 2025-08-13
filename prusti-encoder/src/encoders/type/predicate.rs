use std::ops::{Deref, DerefMut};

use prusti_rustc_interface::{
    middle::ty::{self, TyKind},
    abi,
};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{
    CallableIdn, CastType, FunctionIdn, HasType, MethodIdn, PredicateIdn,
    VirCtxt,
};

use crate::encoders::{domain::DomainEnc, r#type::lifted::generic::LiftedGeneric};

use super::{
    domain::{DomainDataImmRef, DomainDataMutRef, DomainDataPrim, DomainDataStruct},
    lifted::{ty::LiftedTy},
    most_generic_ty::{get_vir_base_name_kind, MostGenericTy},
};

/// Takes a `MostGenericTy` and returns various Viper predicates and functions for
/// working with the type.
pub(super) struct PredicateEnc;

#[derive(Clone, Debug)]
pub enum PredicateEncError {
    // UnsupportedType,
}

#[derive(Clone, Copy, Debug)]
pub struct PredicateEncDataStruct<'vir> {
    pub snap_data: DomainDataStruct<'vir>,
    /// Ref to self as argument. Returns Ref to field.
    pub ref_to_field_refs: &'vir [FunctionIdn<'vir, (vir::Ref, vir::ManyTyVal), vir::Ref>],
}

#[derive(Clone, Copy, Debug)]
pub struct PredicateEncDataEnum<'vir> {
    pub discr: FunctionIdn<'vir, vir::Ref, vir::Ref>,
    pub discr_prim: DomainDataPrim<'vir>,
    //pub discr_bounds: DiscrBounds<'vir>,
    // pub snap_to_discr_snap: FunctionIdn<'vir, UnaryArity<'vir>>,
    pub variants: &'vir [PredicateEncDataVariant<'vir>],
}
#[derive(Clone, Copy, Debug)]
pub struct PredicateEncDataVariant<'vir> {
    pub predicate: PredicateIdn<'vir, (vir::Ref, vir::ManyTyVal)>,
    pub vid: abi::VariantIdx,
    pub discr: vir::ExprCSnap<'vir>,
    pub fields: PredicateEncDataStruct<'vir>,
}

#[derive(Clone, Copy, Debug)]
pub struct PredicateEncDataImmRef<'vir> {
    pub deref_func: vir::FunctionIdn<'vir, (vir::Ref, vir::ManyTyVal), vir::Ref>,
    pub perm: Option<vir::ExprPerm<'vir>>,
    pub snap_data: DomainDataImmRef<'vir>,
}

#[derive(Clone, Copy, Debug)]
pub struct PredicateEncDataMutRef<'vir> {
    pub deref_func: vir::FunctionIdn<'vir, vir::Ref, vir::Ref>,
    pub perm: Option<vir::ExprPerm<'vir>>,
    pub snap_data: DomainDataMutRef<'vir>,
}

#[derive(Clone, Copy, Debug)]
pub enum PredicateEncData<'vir> {
    Never,
    Primitive(DomainDataPrim<'vir>),
    // structs, tuples
    Trusted,
    StructLike(PredicateEncDataStruct<'vir>),
    EnumLike(Option<PredicateEncDataEnum<'vir>>),
    ImmRef(PredicateEncDataImmRef<'vir>),
    MutRef(PredicateEncDataMutRef<'vir>),
    Param,
}

pub type RefToIndirectPred<'vir> = i32; //vir::ExprGen<'vir, vir::Expr<'vir>, vir::ExprKind<'vir>>;

// TODO: should output refs actually be references to structs...?
#[derive(Clone, Copy, Debug)]
pub struct PredicateEncOutputRef<'vir> {
    /// Constructs the Viper predicate application.
    pub ref_to_pred: PredicateIdn<'vir, (vir::Ref, vir::ManyTyVal)>,
    /// Construct snapshot from Viper ref.
    pub ref_to_snap: FunctionIdn<'vir, (vir::Ref, vir::ManyTyVal), vir::Snap>,
    /// Ref as first argument, followed by type parameters, followed by
    /// snapshot. Ensures predicate access to ref with snapshot value. This
    /// probably shouldn't be accessed directly, instead see
    /// `TyImpureEncOutputRef::apply_method_assign`.
    pub(super) method_assign: MethodIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::Snap)>,
    /// Always `TypeData::Domain`.
    pub snapshot: vir::TypeSnap<'vir>,
    //pub method_refold: &'vir str,
    pub specifics: PredicateEncData<'vir>,
    #[allow(dead_code)]
    pub generics: &'vir [vir::LocalDeclTyVal<'vir>],

    //pub ref_to_lifetime_pred: HashMap<ty::Region<'vir>, ()>,
    pub ref_to_indirect_pred: Option<RefToIndirectPred<'vir>>,
}
impl<'vir> task_encoder::OutputRefAny for PredicateEncOutputRef<'vir> {}

impl<'vir> PredicateEncOutputRef<'vir> {
    #[track_caller]
    pub fn expect_prim(&self) -> DomainDataPrim<'vir> {
        match self.specifics {
            PredicateEncData::Primitive(prim) => prim,
            _ => panic!("expected primitive type"),
        }
    }
    #[track_caller]
    pub fn expect_immref(&self) -> PredicateEncDataImmRef<'vir> {
        match self.specifics {
            PredicateEncData::ImmRef(r) => r,
            s => panic!("expected immref type ({s:?})"),
        }
    }
    #[track_caller]
    pub fn expect_mutref(&self) -> PredicateEncDataMutRef<'vir> {
        match self.specifics {
            PredicateEncData::MutRef(r) => r,
            s => panic!("expected mutref type ({s:?})"),
        }
    }
    pub fn get_structlike(&self) -> Option<&PredicateEncDataStruct<'vir>> {
        match &self.specifics {
            PredicateEncData::StructLike(data) => Some(data),
            _ => None,
        }
    }
    #[track_caller]
    pub fn expect_structlike(&self) -> &PredicateEncDataStruct<'vir> {
        self.get_structlike().expect("expected structlike type")
    }
    pub fn get_enumlike(&self) -> Option<&Option<PredicateEncDataEnum<'vir>>> {
        match &self.specifics {
            PredicateEncData::EnumLike(e) => Some(e),
            _ => None,
        }
    }
    #[track_caller]
    pub fn expect_enumlike(&self) -> Option<&PredicateEncDataEnum<'vir>> {
        self.get_enumlike()
            .expect("expected enumlike type")
            .as_ref()
    }
    pub fn get_variant_any(&self, vid: abi::VariantIdx) -> &PredicateEncDataStruct<'vir> {
        match &self.specifics {
            PredicateEncData::StructLike(s) => {
                assert_eq!(vid, abi::FIRST_VARIANT);
                s
            }
            PredicateEncData::EnumLike(e) => &e.as_ref().unwrap().variants[vid.as_usize()].fields,
            _ => panic!("expected structlike or enumlike type"),
        }
    }

    #[track_caller]
    pub fn expect_variant(&self, vid: abi::VariantIdx) -> &PredicateEncDataVariant<'vir> {
        match &self.specifics {
            PredicateEncData::EnumLike(e) => &e.as_ref().unwrap().variants[vid.as_usize()],
            _ => panic!("expected enum type"),
        }
    }
    #[track_caller]
    pub fn expect_pred_variant_opt(
        &self,
        vid: Option<abi::VariantIdx>,
    ) -> PredicateIdn<'vir, (vir::Ref, vir::ManyTyVal)> {
        vid.map(|vid| self.expect_variant(vid).predicate)
            .unwrap_or(self.ref_to_pred)
    }

    pub fn get_ref_to_pred(
        &self,
        vid: Option<abi::VariantIdx>,
    ) -> PredicateIdn<'vir, (vir::Ref, vir::ManyTyVal)> {
        vid.map(|vid| {
            let data = self.expect_enumlike().expect("empty enum");
            data.variants[vid.as_usize()].predicate
        }).unwrap_or(self.ref_to_pred)
    }

    /// Returns `None` if the `vid` is `None` and this is an enum.
    pub fn get_variant_opt(
        &self,
        vid: Option<abi::VariantIdx>,
    ) -> Option<&PredicateEncDataStruct<'vir>> {
        match vid {
            None => self.get_structlike(),
            Some(vid) => {
                Some(&self.expect_enumlike().expect("empty enum").variants[vid.as_usize()].fields)
            }
        }
    }
}

pub(crate) struct PredicateBuilder<'vir> {
    pub(crate) generic_decls: Vec<vir::LocalDeclTyVal<'vir>>,
    pub(crate) generic_exprs: Vec<vir::ExprTyVal<'vir>>,
    pub(crate) generic_tys: &'vir [vir::TypeTyVal<'vir>],

    pub(crate) inner: PredicateBuilderInner<'vir>,
}

/// Holds everything built up to this point.
pub(crate) struct PredicateBuilderInner<'vir> {
    pub(crate) vcx: &'vir vir::VirCtxt<'vir>,
    name: Option<&'vir str>,

    pub(crate) fields: Vec<vir::FieldDyn<'vir>>,
    pub(crate) predicates: Vec<vir::Predicate<'vir>>,
    pub(crate) functions: Vec<vir::Function<'vir>>,
    pub(crate) methods: Vec<vir::Method<'vir>>,

    // TODO: function idents!
    pub(crate) function_snap: Option<vir::Function<'vir>>,
}

impl<'vir> PredicateBuilder<'vir> {
    pub(crate) fn new(vcx: &'vir vir::VirCtxt<'vir>, ty: MostGenericTy) -> Self {
        let generic_decls = ty.generic_decls(vcx);
        let generic_exprs = ty.generic_exprs(vcx);
        let generic_tys = ty.generic_tys(vcx);
        PredicateBuilder {
            generic_decls,
            generic_exprs,
            generic_tys: vcx.alloc_slice(&generic_tys),
            inner: PredicateBuilderInner {
                vcx,
                name: None,
                fields: Vec::new(),
                functions: Vec::new(),
                methods: Vec::new(),
                predicates: Vec::new(),
                function_snap: None,
            },
        }
    }

    fn set_opaque(&mut self, snapshot: vir::TypeSnap<'vir>, ref_self_decl: &vir::LocalDeclRef<'vir>) {
        // TODO: breakout to separate file
        self.inner.predicate::<(vir::Ref, vir::ManyTyVal)>(
            "",
            (ref_self_decl.ty(), self.generic_tys),
            (ref_self_decl, &self.generic_decls),
            None,
        );
        self.function_snap = Some(
            self
                .mk_function::<(vir::Ref, vir::ManyTyVal), _>(
                    "snap",
                    (ref_self_decl.ty(), self.generic_tys),
                    snapshot,
                    (ref_self_decl, &self.generic_decls),
                    &[],
                    &[],
                    None,
                )
                .1,
        );
    }
}

impl<'vir> Deref for PredicateBuilder<'vir> {
    type Target = PredicateBuilderInner<'vir>;
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<'vir> DerefMut for PredicateBuilder<'vir> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl<'vir> PredicateBuilderInner<'vir> {
    pub(crate) fn set_name(&mut self, name: &str) {
        let name = vir::vir_format!(self.vcx, "p_{name}");
        self.name = Some(name);
    }

    fn ident_str(&self, name: &str) -> &'vir str {
        let prefix = self.name.expect("name should be set");
        if name.is_empty() {
            prefix
        } else {
            vir::vir_format!(self.vcx, "{prefix}_{name}")
        }
    }

    pub(crate) fn field<T: vir::CompType>(
        &mut self,
        name: &str,
        typ: vir::Type<'vir, T>,
    ) -> vir::Field<'vir, T> {
        let name = self.ident_str(name);
        let field = self.vcx.mk_field(name, typ);
        self.fields.push(field.as_dyn());
        field
    }

    pub(crate) fn predicate_ident<A: vir::Arity>(
        &mut self,
        name: &str,
        args: A::Tys<'vir>,
    ) -> vir::PredicateIdn<'vir, A> {
        let name = self.ident_str(name);
        let ident = vir::PredicateIdn::new(vir::ViperIdent::new(name), args);
        ident
    }

    pub(crate) fn predicate<A: vir::Arity>(
        &mut self,
        name: &str,
        args: A::Tys<'vir>,
        params: A::Locals<'_, 'vir>,
        expr: Option<vir::ExprBool<'vir>>,
    ) -> vir::PredicateIdn<'vir, A> {
        let ident = self.predicate_ident(name, args);
        self.predicates.push(
            self.vcx
                .mk_predicate(ident, params, expr),
        );
        ident
    }

    pub(crate) fn function_ident<A: vir::Arity, T: vir::CompType>(
        &mut self,
        name: &str,
        args: A::Tys<'vir>,
        ret: vir::Type<'vir, T>,
    ) -> vir::FunctionIdn<'vir, A, T> {
        let name = self.ident_str(name);
        let ident = vir::FunctionIdn::new(vir::ViperIdent::new(name), args, ret);
        ident
    }

    pub(crate) fn mk_function<A: vir::Arity, T: vir::CompType>(
        &self,
        name: &str,
        args: A::Tys<'vir>,
        ret: vir::Type<'vir, T>,
        params: A::Locals<'_, 'vir>,
        pres: &[vir::ExprBool<'vir>],
        posts: &[vir::ExprBool<'vir>],
        expr: Option<vir::Expr<'vir, T>>,
    ) -> (vir::FunctionIdn<'vir, A, T>, vir::Function<'vir>) {
        let name = self.ident_str(name);
        let ident = vir::FunctionIdn::new(vir::ViperIdent::new(name), args, ret);
        (
            ident,
            self.vcx.mk_function(
                ident,
                params,
                self.vcx.alloc_slice(pres),
                self.vcx.alloc_slice(posts),
                None,
                expr,
            ),
        )
    }

    pub(crate) fn function<A: vir::Arity, T: vir::CompType>(
        &mut self,
        name: &str,
        args: A::Tys<'vir>,
        ret: vir::Type<'vir, T>,
        params: A::Locals<'_, 'vir>,
        pres: &[vir::ExprBool<'vir>],
        posts: &[vir::ExprBool<'vir>],
        expr: Option<vir::Expr<'vir, T>>,
    ) -> vir::FunctionIdn<'vir, A, T> {
        let (ident, function) = self.mk_function(name, args, ret, params, pres, posts, expr);
        self.functions.push(function);
        ident
    }

    pub(crate) fn method<A: vir::Arity>(
        &mut self,
        name: &str,
        args: A::Tys<'vir>,
        rets: &[vir::LocalDeclDyn<'vir>],
        params: A::Locals<'_, 'vir>,
        pres: &[vir::ExprBool<'vir>],
        posts: &[vir::ExprBool<'vir>],
    ) -> vir::MethodIdn<'vir, A> {
        let name = self.ident_str(name);
        let ident = MethodIdn::new(
            vir::ViperIdent::new(name),
            args,
            //ret,
        );
        self.methods.push(self.vcx.mk_method(
            ident,
            params,
            self.vcx.alloc_slice(rets),
            self.vcx.alloc_slice(pres),
            self.vcx.alloc_slice(posts),
            None,
        ));
        ident
    }

    pub(crate) fn build(self) -> PredicateEncOutput<'vir> {
        PredicateEncOutput {
            fields: self.fields,
            predicates: self.predicates,
            function_snap: self.function_snap.unwrap(),
            ref_to_field_refs: self.functions,
            method_assign: self.methods[0],
        }
    }
}

#[derive(Clone, Debug)]
pub struct PredicateEncOutput<'vir> {
    pub fields: Vec<vir::FieldDyn<'vir>>,
    pub predicates: Vec<vir::Predicate<'vir>>,
    pub function_snap: vir::Function<'vir>,
    pub ref_to_field_refs: Vec<vir::Function<'vir>>,
    pub method_assign: vir::Method<'vir>,
}

impl PredicateEnc {
    pub fn generic_predicate<'vir, E: TaskEncoder + 'vir + ?Sized>(deps: &mut TaskEncoderDependencies<'vir, E>) -> PredicateEncOutputRef<'vir> {
        deps.require_ref::<PredicateEnc>(MostGenericTy::param()).unwrap()
    }
}

impl TaskEncoder for PredicateEnc {
    task_encoder::encoder_cache!(PredicateEnc);

    type TaskDescription<'vir> = MostGenericTy<'vir>;

    type OutputRef<'vir> = PredicateEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = PredicateEncOutput<'vir>;
    //type OutputFullDependency<'vir> = PredicateEncOutputDep<'vir>;

    type EncodingError = PredicateEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let snap = deps.require_dep::<DomainEnc>(*task_key)?;
        let snapshot = (snap.domain)();

        if let Some(res) = vir::with_vcx(|vcx| {
            let mut builder = PredicateBuilder::new(vcx, *task_key);

            let base_name = get_vir_base_name_kind(task_key.kind(), vcx);
            builder.set_name(&base_name);

            let ref_self = vcx.mk_local("self", vir::TYPE_REF);
            let ref_self_decl = vcx.mk_local_decl_local(ref_self);

            let self_pred_ident =
                builder.inner.predicate_ident("", (ref_self_decl.ty(), builder.generic_tys));
            let snap_func_ident = builder.inner.function_ident::<(vir::Ref, vir::ManyTyVal), vir::Snap>(
                "snap",
                (ref_self_decl.ty(), builder.generic_tys),
                snapshot,
            );

            // assign method
            let value = vcx.mk_local("value", snapshot);
            let method_assign = builder.inner.method(
                "assign",
                (ref_self_decl.ty(), builder.generic_tys, snapshot),
                &[],
                (ref_self_decl, builder.generic_decls.as_slice(), vcx.mk_local_decl_local(value)),
                &[],
                &[
                    vir::expr! { [self_pred_ident](ref_self, ..[builder.generic_exprs.as_slice()]) },
                    vir::expr! { ([snap_func_ident](ref_self, ..[builder.generic_exprs.as_slice()])) == (value) },
                ],
            );

            let (specifics, ref_to_indirect_pred) = match task_key.kind() {
                _ if crate::encoders::spec::is_type_trusted(task_key.ty()) => {
                    builder.set_opaque(snapshot, &ref_self_decl);
                    (PredicateEncData::Trusted, None)
                }
                TyKind::Bool
                | TyKind::Char
                | TyKind::Int(_)
                | TyKind::Uint(_)
                | TyKind::Float(_) => {
                    super::kinds::primitive::predicate(*task_key, snap.clone(), deps, &mut builder)?
                }
                TyKind::Adt(..) => super::kinds::adt::predicate(
                    *task_key,
                    snap.clone(),
                    deps,
                    &mut builder,
                )?,
                TyKind::Ref(_, _, ty::Mutability::Not) => super::kinds::immref::predicate(
                    *task_key,
                    snap.clone(),
                    deps,
                    &mut builder,
                )?,
                TyKind::Ref(_, _, ty::Mutability::Mut) => super::kinds::mutref::predicate(
                    *task_key,
                    snap.clone(),
                    deps,
                    /*&generic_decls, &generic_exprs, */ &mut builder,
                )?,
                TyKind::Never => (
                    super::kinds::never::predicate(
                        *task_key,
                        snap.clone(),
                        deps,
                        /*&generic_decls, &generic_exprs, */ &mut builder,
                    )?,
                    None,
                ),
                TyKind::Closure(..) => (
                    super::kinds::closure::predicate(
                        *task_key,
                        snap.clone(),
                        deps,
                        &mut builder,
                    )?,
                    None,
                ),
                TyKind::Tuple(..) => (
                    super::kinds::tuple::predicate(
                        *task_key,
                        snap.clone(),
                        deps,
                        &mut builder,
                    )?,
                    None,
                ),
                TyKind::Str => (
                    super::kinds::str::predicate(*task_key, snap.clone(), deps, &mut builder)?,
                    None,
                ),
                TyKind::Param(_) => {
                    builder.set_opaque(snapshot, &ref_self_decl);
                    (PredicateEncData::Param, None)
                }
                _ => return Ok(None),
            };

            deps.emit_output_ref(
                *task_key,
                PredicateEncOutputRef {
                    ref_to_pred: self_pred_ident,
                    ref_to_snap: snap_func_ident.cast_ty(snap_func_ident.arity()),
                    method_assign,
                    snapshot,
                    specifics,
                    generics: vcx.alloc_slice(&builder.generic_decls),
                    ref_to_indirect_pred,
                },
            )?;

            Ok(Some(builder.inner.build()))
        })? {
            return Ok((res, ()));
        }

        match task_key.kind() {
            TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) => {
                unreachable!()
            }
            TyKind::Adt(..) => unreachable!(),
            TyKind::Ref(..) => unreachable!(),
            TyKind::Param(_) => unreachable!(),
            TyKind::Closure(..) => unreachable!(),
            TyKind::Never => unreachable!(),
            TyKind::Tuple(..) => unreachable!(),
            TyKind::Str => unreachable!(),
            unsupported_type => todo!("type not supported: {unsupported_type:?}"),
        }
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local() {
            for field in output.fields {
                program.add_field(field);
            }
            for field_projection in output.ref_to_field_refs {
                program.add_function(field_projection);
            }
            program.add_function(output.function_snap);
            for pred in output.predicates {
                program.add_predicate(pred);
            }
            program.add_method(output.method_assign);
        }
    }
}

fn mk_method_assign<'vir>(
    vcx: &'vir VirCtxt<'_>,
    ident: MethodIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::Snap)>,
    generics: Vec<vir::LocalDeclTyVal<'vir>>,
    snapshot: vir::TypeSnap<'vir>,
    ref_to_pred: PredicateIdn<'vir, (vir::Ref, vir::ManyTyVal)>,
    ref_to_snap: FunctionIdn<'vir, (vir::Ref, vir::ManyTyVal), vir::Snap>,
) -> vir::Method<'vir> {
    let self_local = vcx.mk_local_decl("self", vir::TYPE_REF);
    let self_new_local = vcx.mk_local_decl("self_new", snapshot);

    let self_arg = vcx.mk_local_ex(self_local.name, self_local.ty);
    let generic_args = generics
        .iter()
        .copied()
        .map(|decl| vcx.mk_local_ex(decl.name, decl.ty))
        .collect::<Vec<_>>();

    let self_pred_app = vcx.mk_predicate_app_expr(ref_to_pred(self_arg, &generic_args)(None));

    let assign_args = (self_local, generics.as_slice(), self_new_local);

    let posts = vcx.alloc_slice(&[
        self_pred_app,
        vcx.mk_eq_expr(
            ref_to_snap(self_arg, &generic_args),
            vcx.mk_local_ex(self_new_local.name, snapshot),
        ),
    ]);
    vcx.mk_method(ident, assign_args, &[], &[], posts, None)
}
