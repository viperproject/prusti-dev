use std::ops::{Deref, DerefMut};

use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CallableIdn, CastType, FunctionIdn, HasType, MethodIdn, PredicateIdn};

use crate::encoders::{Impure, ty::use_impure::TyUseImpure};

use super::{
    RustTy, ViperTyDatas,
    data::*,
    generics::{GenericParams, GenericParamsEnc},
    pure::*,
};

pub(super) type ImpureTyDatas = ViperTyDatas<Impure>;

impl<'vir> TyDatas<'vir> for ImpureTyDatas {
    type TyData = TyImpureRef<'vir>;
    type PrimitiveData = ();
    type ArrayData = TyImpureArrayData<'vir>;
    type ImmRefData = TyImpureImmRefData;
    type MutRefData = TyImpureMutRefData<'vir>;
    type FieldData = TyImpureFieldData<'vir>;
    type StructData = ();
    type VariantData = TyImpureVariantData<'vir>;
    type EnumData = TyImpureEnumData<'vir>;
}

pub type TyImpure<'vir> = Ty<'vir, ImpureTyDatas>;
pub type TyImpureParam<'vir> = <ImpureTyDatas as TyDatas<'vir>>::ParamData;
pub type TyImpureOpaque<'vir> = <ImpureTyDatas as TyDatas<'vir>>::OpaqueData;
pub type TyImpurePrimitive<'vir> = <ImpureTyDatas as TyDatas<'vir>>::PrimitiveData;
pub type TyImpureImmRef<'vir> = <ImpureTyDatas as TyDatas<'vir>>::ImmRefData;
pub type TyImpureMutRef<'vir> = <ImpureTyDatas as TyDatas<'vir>>::MutRefData;

#[derive(Debug, Clone, Copy)]
pub struct TyImpureImmRefData {}

#[derive(Debug, Clone, Copy)]
pub struct TyImpureMutRefData<'vir> {
    pub deref_func: vir::FunctionIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::ManyCSnap), vir::Ref>,
}

#[derive(Debug, Clone, Copy)]
pub struct TyImpureArrayData<'vir> {
    pub index_access: vir::FunctionIdn<'vir, (vir::Ref, vir::Int), vir::Ref>,
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
    pub inhabited: bool,
    /// Constructs the Viper predicate application.
    pub ref_to_pred: PredicateIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>,
    /// Construct snapshot from Viper ref.
    pub ref_to_snap: FunctionIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>,
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
    pub function_snap: vir::Function<'vir>,
    pub ref_to_field_refs: Vec<vir::Function<'vir>>,
    pub method_assign: vir::Method<'vir>,
    pub methods: Vec<vir::Method<'vir>>,
}

impl TaskEncoder for TyImpureEnc {
    task_encoder::encoder_cache!(TyImpureEnc);
    type TaskDescription<'vir> = RustTy<'vir>;

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
        deps.emit_output_ref(*task_key, ())?;
        let snap = deps.require_dep::<TyPureEnc>(*task_key)?;
        let snapshot = (snap.domain)();

        let ty = task_key.zip(snap);

        vir::with_vcx(|vcx| {
            let mut builder = PredicateBuilder::new(deps, vcx, task_key, snapshot);

            let ref_self_decl = builder.ref_self_decl();
            let ref_self = vcx.mk_local_ex(ref_self_decl);

            let self_pred_ident = builder.inner.predicate_ident(
                "",
                (
                    ref_self_decl.ty(),
                    builder.params.ty_args(),
                    builder.params.const_args(),
                ),
            );
            let snap_func_ident = builder
                .inner
                .function_ident::<(vir::Ref, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>(
                    "snap",
                    (
                        ref_self_decl.ty(),
                        builder.params.ty_args(),
                        builder.params.const_args(),
                    ),
                    snapshot,
                );

            // assign method
            let value_decl = vcx.mk_local_decl("value", snapshot);
            let value = vcx.mk_local_ex(value_decl);
            let method_assign = builder.inner.method(
                "assign",
                (ref_self_decl.ty(), builder.params.ty_args(), builder.params.const_args(), snapshot),
                &[],
                (ref_self_decl, builder.params.ty_decls(), builder.params.const_decls(), value_decl),
                &[],
                &[
                    vir::expr! { [self_pred_ident](ref_self, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]]) },
                    vir::expr! { ([snap_func_ident](ref_self, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]])) == (value) },
                ],
            );

            let specifics = match &ty.specifics {
                TySpecifics::Param(param) => {
                    TySpecifics::Param(super::kinds::param::ty_impure(param, deps, &mut builder)?)
                }
                TySpecifics::Opaque(opaque) => TySpecifics::Opaque(
                    super::kinds::opaque::ty_impure(opaque, deps, &mut builder)?,
                ),
                TySpecifics::ArrayLike(array) => {
                    TySpecifics::ArrayLike(super::kinds::arraylike::ty_impure(
                        &ty,
                        array,
                        deps,
                        &mut builder,
                        snap_func_ident,
                    )?)
                }
                TySpecifics::Primitive(prim) => TySpecifics::Primitive(
                    super::kinds::primitive::ty_impure(prim, deps, &mut builder)?,
                ),
                TySpecifics::ImmRef(immref) => TySpecifics::ImmRef(
                    super::kinds::immref::ty_impure(immref, deps, &mut builder)?,
                ),
                TySpecifics::MutRef(mutref) => TySpecifics::MutRef(
                    super::kinds::mutref::ty_impure(mutref, deps, &mut builder)?,
                ),
                TySpecifics::StructLike(structlike) => TySpecifics::StructLike(
                    super::kinds::structlike::ty_impure(&ty, structlike, deps, &mut builder)?,
                ),
                TySpecifics::EnumLike(enumlike) => TySpecifics::EnumLike(
                    super::kinds::enumlike::ty_impure(&ty, enumlike, deps, &mut builder)?,
                ),
            };
            let data = TyImpureRef {
                inhabited: ty.inhabited,
                ref_to_pred: self_pred_ident,
                ref_to_snap: snap_func_ident.cast_ty(snap_func_ident.arity()),
                method_assign,
            };
            let output = TyData::new(data, ty.inhabited, specifics).alloc();

            Ok((builder.inner.build(), output))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors() {
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
            for method in output.methods {
                program.add_method(method);
            }
        }
    }
}

pub(crate) struct PredicateBuilder<'vir> {
    pub(super) params: GenericParams<'vir>,
    snapshot: vir::TypeSnap<'vir>,

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
    pub(crate) function_snap: Option<vir::Function<'vir>>,
}

impl<'vir> PredicateBuilder<'vir> {
    pub(crate) fn new<E: TaskEncoder>(
        deps: &mut TaskEncoderDependencies<'vir, E>,
        vcx: &'vir vir::VirCtxt<'vir>,
        ty: RustTy<'vir>,
        snapshot: vir::TypeSnap<'vir>,
    ) -> Self {
        let params = deps.require_dep::<GenericParamsEnc>(ty.params).unwrap();
        let name = vir::vir_format!(vcx, "p_{}", ty.name());
        PredicateBuilder {
            params,
            snapshot,
            inner: PredicateBuilderInner {
                vcx,
                name,
                fields: Vec::new(),
                functions: Vec::new(),
                methods: Vec::new(),
                predicates: Vec::new(),
                function_snap: None,
            },
        }
    }

    pub(crate) fn snap_type(&self) -> vir::TypeSnap<'vir> {
        self.snapshot
    }

    pub(crate) fn csnap_type(&self) -> vir::TypeCSnap<'vir> {
        self.snapshot.downcast_ty()
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
        &mut self,
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
        &mut self,
        name: &str,
        args: A::Tys<'vir>,
        ret: vir::Type<'vir, T>,
    ) -> vir::FunctionIdn<'vir, A, T> {
        let name = self.ident_str(name);

        vir::FunctionIdn::new(vir::ViperIdent::new(name), args, ret)
    }

    #[allow(clippy::too_many_arguments)]
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

    pub(crate) fn build(mut self) -> TyImpureEncLocal<'vir> {
        // TODO: don't rely on assignment being index 0, use separate field...
        let method_assign = self.methods.remove(0);
        TyImpureEncLocal {
            fields: self.fields,
            predicates: self.predicates,
            function_snap: self.function_snap.unwrap(),
            ref_to_field_refs: self.functions,
            method_assign,
            methods: self.methods,
        }
    }
}
