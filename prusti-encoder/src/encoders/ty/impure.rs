use std::ops::{Deref, DerefMut};

use pcg::borrow_pcg::region_projection::{ExtractRegionsCtxt, LifetimeProjection};
use task_encoder::{EncodeFullError, EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, FunctionIdn, HasType, MethodIdn, PredicateIdn, Reify};

use crate::encoders::{Impure, ty::use_impure::TyUseImpure};

use super::{
    RustTy, RustTyDecomposition, ViperTyDatas,
    data::*,
    generics::{GenericParams, GenericParamsEnc},
    indirect::{IndirectPredicatesEnc, PrustiPcgCtxt},
    pure::*,
};

pub(super) type ImpureTyDatas = ViperTyDatas<Impure>;

impl<'vir> TyDatas<'vir> for ImpureTyDatas {
    type TyData = TyImpureRef<'vir>;
    type PrimitiveData = ();
    type ArrayData = TyImpureArrayData<'vir>;
    type ImmRefData = TyImpureImmRefData;
    type MutRefData = TyImpureMutRefData<'vir>;
    type RawData = TyImpureRawData;
    type FieldData = TyImpureFieldData<'vir>;
    type StructData = TyImpureStructData<'vir>;
    type VariantData = TyImpureVariantData<'vir>;
    type EnumData = TyImpureEnumData<'vir>;
    type BuiltinData = ();
}

pub type TyImpure<'vir> = Ty<'vir, ImpureTyDatas>;
pub type TyImpureParam<'vir> = <ImpureTyDatas as TyDatas<'vir>>::ParamData;
pub type TyImpureOpaque<'vir> = <ImpureTyDatas as TyDatas<'vir>>::OpaqueData;
pub type TyImpurePrimitive<'vir> = <ImpureTyDatas as TyDatas<'vir>>::PrimitiveData;
pub type TyImpureImmRef<'vir> = <ImpureTyDatas as TyDatas<'vir>>::ImmRefData;
pub type TyImpureMutRef<'vir> = <ImpureTyDatas as TyDatas<'vir>>::MutRefData;
pub type TyImpureRaw<'vir> = <ImpureTyDatas as TyDatas<'vir>>::RawData;
pub type TyImpureBuiltin<'vir> = <ImpureTyDatas as TyDatas<'vir>>::BuiltinData;

#[derive(Debug, Clone, Copy)]
pub struct TyImpureImmRefData {}

#[derive(Debug, Clone, Copy)]
pub struct TyImpureRawData {}

#[derive(Debug, Clone, Copy)]
pub struct TyImpureMutRefData<'vir> {
    pub pure: <PureTyDatas as TyDatas<'vir>>::MutRefData,
    /// The value slot of the *shallow* snapshot: a shallow snapshot holds no
    /// permission to the referent, so its value is unconstrained. Takes the
    /// referent's type arguments so that it is not shared between
    /// instantiations at different types. Only the deep snapshot (see
    /// `ref_to_deep_snap`) carries the referent's actual value.
    pub arbitrary_value:
        vir::FunctionIdn<'vir, (vir::Ref, vir::PSnap, vir::ManyTyVal, vir::ManyCSnap), vir::CSnap>,
}

#[derive(Debug, Clone, Copy)]
pub struct TyImpureStructData<'vir> {
    /// The hardcoded extras when this struct is a `Box`.
    pub box_data: Option<TyImpureBoxData<'vir>>,
}

/// The hardcoded extras of a `Box`: the pointer metadata, read out of the
/// (folded) `Unique` predicate (the value field's address accessor is the
/// similarly heap-dependent `address` function in its `TyImpureFieldData`).
#[derive(Debug, Clone, Copy)]
pub struct TyImpureBoxData<'vir> {
    pub metadata: FunctionIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::ManyCSnap), vir::PSnap>,
}

#[derive(Debug, Clone, Copy)]
pub struct TyImpureArrayData<'vir> {
    /// Function to access the ref at the given index.
    pub ref_to_index_ref: vir::FunctionIdn<'vir, (vir::Ref, vir::Int, vir::ManyTyVal), vir::Ref>,
    #[allow(dead_code)]
    pub index_frame:
        vir::FunctionIdn<'vir, (vir::Ref, vir::Int, vir::ManyTyVal, vir::ManyCSnap), vir::CSnap>,
    #[allow(dead_code)]
    pub index_predicate: PredicateIdn<'vir, (vir::Ref, vir::Int, vir::ManyTyVal, vir::ManyCSnap)>,
    pub method_fold: vir::MethodIdn<'vir, (vir::Int, vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>,
    pub method_unfold: vir::MethodIdn<'vir, (vir::Int, vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>,
}

#[derive(Debug, Clone, Copy)]
pub struct TyImpureFieldData<'vir> {
    pub ref_to_field_ref: FunctionIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::ManyCSnap), vir::Ref>,
}

#[derive(Debug, Clone, Copy)]
pub struct TyImpureEnumData<'vir> {
    pub(super) discr: FunctionIdn<'vir, vir::Ref, vir::Ref>,
    pub(super) discr_ty: TyUseImpure<'vir>,
}

#[derive(Debug, Clone, Copy)]
pub struct TyImpureVariantData<'vir> {
    pub predicate: PredicateIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>,
}

/// You probably never want to use this, use `TyUseImpureEnc` instead.
pub(super) type TyImpureEnc = super::TyEnc<Impure>;

#[derive(Clone, Debug)]
pub enum TyImpureEncError {
    // UnsupportedType,
}

// TODO: should output refs actually be references to structs...?
#[derive(Debug, Clone, Copy)]
pub struct TyImpureRef<'vir> {
    /// Constructs the Viper predicate application.
    pub ref_to_pred: PredicateIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>,
    /// Construct deep snapshot from Viper ref.
    pub ref_to_deep_snap: FunctionIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>,
    /// Construct shallow snapshot from Viper ref.
    pub ref_to_shallow_snap:
        FunctionIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>,
    /// Ref as first argument, followed by type parameters, followed by
    /// snapshot. Ensures predicate access to ref with snapshot value. This
    /// probably shouldn't be accessed directly, instead see
    /// `TyImpureEncLocalRef::apply_method_assign`.
    pub(super) method_assign:
        MethodIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::ManyCSnap, vir::Snap)>,
}

impl<'vir> task_encoder::OutputRefAny for TyImpureRef<'vir> {}

#[derive(Clone, Debug)]
pub struct TyImpureEncLocal<'vir> {
    pub fields: Vec<vir::FieldDyn<'vir>>,
    pub predicates: Vec<vir::Predicate<'vir>>,
    pub function_shallow_snap: vir::Function<'vir>,
    /// `None` if the type does not construct a separate deep snapshot.
    pub function_deep_snap: Option<vir::Function<'vir>>,
    pub functions: Vec<vir::Function<'vir>>,
    pub method_assign: vir::Method<'vir>,
    pub methods: Vec<vir::Method<'vir>>,
}

impl TaskEncoder for TyImpureEnc {
    task_encoder::encoder_cache!(TyImpureEnc);
    const ENCODER_NAME: &'static str = "type impure encoder";
    type TaskDescription<'vir> = RustTy<'vir>;

    type OutputRef<'vir> = TyImpureRef<'vir>;
    type OutputFullDependency<'vir> = TyImpure<'vir>;
    type OutputFullLocal<'vir> = TyImpureEncLocal<'vir>;

    type EncodingError = TyImpureEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let snap = deps.require_dep::<TyPureEnc>(*task_key)?;
        let deep_snapshot = snap.deep_snapshot;
        let shallow_snapshot = snap.shallow_snapshot;

        let ty = task_key.zip(snap);

        vir::with_vcx(|vcx| {
            let mut builder =
                PredicateBuilder::new(deps, vcx, task_key, deep_snapshot, shallow_snapshot);

            let ref_self_decl = builder.ref_self_decl();
            let ref_self = vcx.mk_local_ex(ref_self_decl);

            // assign method
            let value_decl = vcx.mk_local_decl("value", shallow_snapshot);
            let value = vcx.mk_local_ex(value_decl);
            let method_assign = builder.inner.method(
                "assign",
                (ref_self_decl.ty(), builder.params.ty_args(), builder.params.const_args(), shallow_snapshot),
                &[],
                (ref_self_decl, builder.params.ty_decls(), builder.params.const_decls(), value_decl),
                &[],
                &[
                    vir::expr! { [builder.ref_to_pred](ref_self, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]]) },
                    vir::expr! { ([builder.ref_to_shallow_snap](ref_self, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]])) == (value) },
                ],
            );

            let data = TyImpureRef {
                ref_to_pred: builder.ref_to_pred,
                ref_to_deep_snap: builder.ref_to_deep_snap,
                ref_to_shallow_snap: builder.ref_to_shallow_snap,
                method_assign,
            };
            deps.emit_output_ref(*task_key, data)?;

            let specifics = match &ty.specifics {
                TySpecifics::Param(param) => {
                    TySpecifics::Param(super::kinds::param::ty_impure(param, deps, &mut builder)?)
                }
                TySpecifics::Opaque(opaque) => TySpecifics::Opaque(
                    super::kinds::opaque::ty_impure(opaque, deps, &mut builder)?,
                ),
                TySpecifics::ArrayLike(array) => TySpecifics::ArrayLike(
                    super::kinds::arraylike::ty_impure(&ty, array, deps, &mut builder)?,
                ),
                TySpecifics::Primitive(prim) => TySpecifics::Primitive(
                    super::kinds::primitive::ty_impure(prim, deps, &mut builder)?,
                ),
                TySpecifics::ImmRef(immref) => TySpecifics::ImmRef(
                    super::kinds::immref::ty_impure(&ty, immref, deps, &mut builder)?,
                ),
                TySpecifics::MutRef(mutref) => TySpecifics::MutRef(
                    super::kinds::mutref::ty_impure(&ty, mutref, deps, &mut builder)?,
                ),
                TySpecifics::Raw(raw) => {
                    TySpecifics::Raw(super::kinds::raw::ty_impure(&ty, raw, deps, &mut builder)?)
                }
                TySpecifics::StructLike(structlike) => TySpecifics::StructLike(
                    super::kinds::structlike::ty_impure(&ty, structlike, deps, &mut builder)?,
                ),
                TySpecifics::EnumLike(enumlike) => TySpecifics::EnumLike(
                    super::kinds::enumlike::ty_impure(&ty, enumlike, deps, &mut builder)?,
                ),
                TySpecifics::Builtin(builtin) => TySpecifics::Builtin(
                    super::kinds::builtin::ty_impure(builtin, deps, &mut builder)?,
                ),
            };
            let output = TyData::new(data, specifics).alloc();

            Ok((builder.build(), output))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors(program) {
            for field in output.fields {
                program.add_field(field);
            }
            for field_projection in output.functions {
                program.add_function(field_projection);
            }
            program.add_function(output.function_shallow_snap);
            if let Some(function_deep_snap) = output.function_deep_snap {
                program.add_function(function_deep_snap);
            }
            for pred in output.predicates {
                program.add_predicate(pred);
            }
            program.add_method(output.method_assign);
            for method in output.methods {
                program.add_method(method);
            }
        }
    }
}

pub(crate) struct PredicateBuilder<'vir> {
    pub(super) params: GenericParams<'vir>,
    deep_snapshot: vir::TypeSnap<'vir>,
    shallow_snapshot: vir::TypeSnap<'vir>,
    /// See `RustTyData::construct_deep_snapshot`.
    construct_deep_snapshot: bool,
    ty: RustTy<'vir>,
    pub(super) ref_to_pred: PredicateIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>,
    pub(super) ref_to_deep_snap:
        FunctionIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>,
    pub(super) ref_to_shallow_snap:
        FunctionIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>,

    pub(super) inner: PredicateBuilderInner<'vir>,
}

/// Holds everything built up to this point.
pub(crate) struct PredicateBuilderInner<'vir> {
    pub(super) vcx: &'vir vir::VirCtxt<'vir>,
    name: &'vir str,

    pub(crate) fields: Vec<vir::FieldDyn<'vir>>,
    pub(crate) predicates: Vec<vir::Predicate<'vir>>,
    pub(crate) functions: Vec<vir::Function<'vir>>,
    pub(crate) methods: Vec<vir::Method<'vir>>,

    // TODO: function idents!
    pub(crate) function_shallow_snap: Option<vir::Function<'vir>>,
    pub(crate) function_deep_snap: Option<vir::Function<'vir>>,
}

impl<'vir> PredicateBuilder<'vir> {
    pub(crate) fn new<E: TaskEncoder>(
        deps: &mut TaskEncoderDependencies<'vir, E>,
        vcx: &'vir vir::VirCtxt<'vir>,
        ty: RustTy<'vir>,
        deep_snapshot: vir::TypeSnap<'vir>,
        shallow_snapshot: vir::TypeSnap<'vir>,
    ) -> Self {
        let params = deps.require_dep::<GenericParamsEnc>(ty.params).unwrap();
        let name = vir::vir_format!(vcx, "p_{}", ty.name());
        let inner = PredicateBuilderInner {
            vcx,
            name,
            fields: Vec::new(),
            functions: Vec::new(),
            methods: Vec::new(),
            predicates: Vec::new(),
            function_shallow_snap: None,
            function_deep_snap: None,
        };

        let ref_self_decl = inner.ref_self_decl();
        let args = (ref_self_decl.ty(), params.ty_args(), params.const_args());
        let ref_to_pred = inner.predicate_ident("", args);
        let (ref_to_deep_snap, ref_to_shallow_snap) = if ty.construct_deep_snapshot {
            (
                inner.function_ident("deep_snap", args, deep_snapshot),
                inner.function_ident("shallow_snap", args, shallow_snapshot),
            )
        } else {
            let snap = inner.function_ident("snap", args, shallow_snapshot);
            (snap, snap)
        };

        PredicateBuilder {
            params,
            deep_snapshot,
            shallow_snapshot,
            construct_deep_snapshot: ty.construct_deep_snapshot,
            ty,
            ref_to_pred,
            ref_to_deep_snap,
            ref_to_shallow_snap,
            inner,
        }
    }

    pub(crate) fn csnap_type_deep(&self) -> vir::TypeCSnap<'vir> {
        self.deep_snapshot.downcast_ty()
    }

    pub(crate) fn csnap_type_shallow(&self) -> vir::TypeCSnap<'vir> {
        self.shallow_snapshot.downcast_ty()
    }

    pub(crate) fn mk_predicate(
        &mut self,
        name: &str,
        expr: Option<vir::ExprBool<'vir>>,
    ) -> PredicateIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::ManyCSnap)> {
        let ref_self_decl = self.ref_self_decl();
        let args = (
            ref_self_decl.ty(),
            self.params.ty_args(),
            self.params.const_args(),
        );
        let params = (
            ref_self_decl,
            self.params.ty_decls(),
            self.params.const_decls(),
        );
        self.inner.predicate(name, args, params, expr)
    }

    /// The permissions to what the mutable references inside the type point
    /// to, for use as `deep_pres` of a struct or enum. These are the type's
    /// indirect predicates (as in method contracts) for each of its
    /// lifetimes, located through the shallow snapshot so that the deep
    /// snapshot's precondition does not depend on the deep snapshot itself.
    /// Empty if the type does not construct a deep snapshot.
    pub(crate) fn indirect_deep_pres(
        &self,
        deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    ) -> Result<Vec<vir::ExprBool<'vir>>, EncodeFullError<'vir, TyImpureEnc>> {
        if !self.construct_deep_snapshot {
            return Ok(Vec::new());
        }
        let ref_self = self.vcx.mk_local_ex(self.ref_self_decl());
        let shallow_snap = self.ref_to_shallow_snap.call()(
            ref_self,
            self.params.ty_exprs(),
            self.params.const_exprs(),
        );
        let decomp = RustTyDecomposition::identity(self.ty);
        let mut pres = Vec::new();
        for region in PrustiPcgCtxt.extract_regions(decomp) {
            let Some(proj) = LifetimeProjection::new(decomp, region, None, PrustiPcgCtxt) else {
                continue;
            };
            let indirect = deps.require_dep::<IndirectPredicatesEnc>(proj)?;
            pres.extend(
                indirect
                    .predicate_applications
                    .iter()
                    .map(|pred| pred.reify(self.vcx, shallow_snap)),
            );
        }
        Ok(pres)
    }

    /// Creates the `deep_snap` function, sets the precondition to
    /// `acc(ref_to_pred(self, ...)) && deep_pres`, and the body as
    /// `unfolding acc(ref_to_pred(self, ...)) in inner`. Note that the `inner`
    /// will be wrapped in an unfolding and should not include it.
    ///
    /// `deep_pres` are the permissions beyond the type's own predicate that
    /// the deep snapshot reads, i.e. those to the referent of a mutable
    /// reference. They must be framed by the type's predicate: they may only
    /// reach the referent through the *shallow* snapshot, never through the
    /// deep one, which would make the function depend on itself.
    ///
    /// A no-op if the type does not construct a separate deep snapshot, in
    /// which case `ref_to_deep_snap` is the shallow snapshot function.
    pub(crate) fn mk_deep_snap_function(
        &mut self,
        inner: Option<vir::ExprCSnap<'vir>>,
        deep_pres: &[vir::ExprBool<'vir>],
        posts: &[vir::ExprBool<'vir>],
    ) {
        if !self.construct_deep_snapshot {
            return;
        }
        let ref_self_decl = self.ref_self_decl();
        let ref_self = self.vcx.mk_local_ex(ref_self_decl);
        let params = (
            ref_self_decl,
            self.params.ty_decls(),
            self.params.const_decls(),
        );
        let pred = vir::expr! {
            acc([self.ref_to_pred](ref_self, [..[self.params.ty_exprs()]], [..[self.params.const_exprs()]]))
        };
        let pres = std::iter::once(pred)
            .chain(deep_pres.iter().copied())
            .collect::<Vec<_>>();
        let expr = inner.map(|e| vir::expr! {
            unfolding ([self.ref_to_pred](ref_self, [..[self.params.ty_exprs()]], [..[self.params.const_exprs()]])) in (e)
        }.upcast_ty());
        let function = self
            .inner
            .mk_function(self.ref_to_deep_snap, params, &pres, posts, expr);
        self.inner.function_deep_snap = Some(function);
    }

    /// Creates the `shallow_snap` function, sets the precondition to
    /// `acc(ref_to_pred(self, ...))`, and the body as
    /// `unfolding acc(ref_to_pred(self, ...)) in inner`. Note that the `inner`
    /// will be wrapped in an unfolding and should not include it.
    pub(crate) fn mk_shallow_snap_function(
        &mut self,
        inner: Option<vir::ExprCSnap<'vir>>,
        posts: &[vir::ExprBool<'vir>],
    ) {
        let ref_self_decl = self.ref_self_decl();
        let ref_self = self.vcx.mk_local_ex(ref_self_decl);
        let params = (
            ref_self_decl,
            self.params.ty_decls(),
            self.params.const_decls(),
        );
        let pred = vir::expr! {
            acc([self.ref_to_pred](ref_self, [..[self.params.ty_exprs()]], [..[self.params.const_exprs()]]))
        };
        let expr = inner.map(|e| vir::expr! {
            unfolding ([self.ref_to_pred](ref_self, [..[self.params.ty_exprs()]], [..[self.params.const_exprs()]])) in (e)
        }.upcast_ty());
        let function =
            self.inner
                .mk_function(self.ref_to_shallow_snap, params, &[pred], posts, expr);
        self.inner.function_shallow_snap = Some(function);
    }

    /// Finishes the encoding. A kind that constructs a separate deep snapshot
    /// but did not define it (it has nothing that the deep snapshot would
    /// add, e.g. a type parameter) gets one equal to the shallow snapshot.
    pub(crate) fn build(mut self) -> TyImpureEncLocal<'vir> {
        if self.construct_deep_snapshot && self.inner.function_deep_snap.is_none() {
            let ref_self_decl = self.ref_self_decl();
            let ref_self = self.vcx.mk_local_ex(ref_self_decl);
            let params = (
                ref_self_decl,
                self.params.ty_decls(),
                self.params.const_decls(),
            );
            let pred = vir::expr! {
                acc([self.ref_to_pred](ref_self, [..[self.params.ty_exprs()]], [..[self.params.const_exprs()]]))
            };
            let shallow = self.ref_to_shallow_snap.call()(
                ref_self,
                self.params.ty_exprs(),
                self.params.const_exprs(),
            );
            let function =
                self.inner
                    .mk_function(self.ref_to_deep_snap, params, &[pred], &[], Some(shallow));
            self.inner.function_deep_snap = Some(function);
        }
        self.inner.build()
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
    pub(super) fn ref_self_decl(&self) -> vir::LocalDeclRef<'vir> {
        self.vcx.mk_local_decl("self", vir::TYPE_REF)
    }

    fn ident_str(&self, name: &str) -> &'vir str {
        let prefix = self.name;
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
        &self,
        name: &str,
        args: A::Tys<'vir>,
    ) -> vir::PredicateIdn<'vir, A> {
        let name = self.ident_str(name);
        vir::PredicateIdn::new(vir::ViperIdent::new(name), args)
    }

    pub(crate) fn predicate<A: vir::Arity>(
        &mut self,
        name: &str,
        args: A::Tys<'vir>,
        params: A::Locals<'_, 'vir>,
        expr: Option<vir::ExprBool<'vir>>,
    ) -> vir::PredicateIdn<'vir, A> {
        let ident = self.predicate_ident(name, args);
        self.predicates
            .push(self.vcx.mk_predicate(ident, params, expr));
        ident
    }

    pub(crate) fn function_ident<A: vir::Arity, T: vir::CompType>(
        &self,
        name: &str,
        args: A::Tys<'vir>,
        ret: vir::Type<'vir, T>,
    ) -> vir::FunctionIdn<'vir, A, T> {
        let name = self.ident_str(name);

        vir::FunctionIdn::new(vir::ViperIdent::new(name), args, ret)
    }

    fn mk_function<A: vir::Arity, T: vir::CompType>(
        &self,
        ident: FunctionIdn<'vir, A, T>,
        params: A::Locals<'_, 'vir>,
        pres: &[vir::ExprBool<'vir>],
        posts: &[vir::ExprBool<'vir>],
        expr: Option<vir::Expr<'vir, T>>,
    ) -> vir::Function<'vir> {
        self.vcx.mk_function(
            ident,
            params,
            self.vcx.alloc_slice(pres),
            self.vcx.alloc_slice(posts),
            None,
            expr,
        )
    }

    #[allow(clippy::too_many_arguments)]
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
        let name = self.ident_str(name);
        let ident = vir::FunctionIdn::new(vir::ViperIdent::new(name), args, ret);
        self.functions
            .push(self.mk_function(ident, params, pres, posts, expr));
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

    pub(crate) fn build(mut self) -> TyImpureEncLocal<'vir> {
        // TODO: don't rely on assignment being index 0, use separate field...
        let method_assign = self.methods.remove(0);
        TyImpureEncLocal {
            fields: self.fields,
            predicates: self.predicates,
            function_shallow_snap: self.function_shallow_snap.unwrap(),
            function_deep_snap: self.function_deep_snap,
            functions: self.functions,
            method_assign,
            methods: self.methods,
        }
    }
}
