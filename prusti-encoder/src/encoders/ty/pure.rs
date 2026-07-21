// TODO: this lint is something we should fix; to address there should probably
//   be an indirection in error storage somewhere, maybe even in `task-encoder`?
#![allow(clippy::result_large_err)]

use std::ops::Deref;

use prusti_rustc_interface::{
    abi,
    middle::ty::{self, IntTy, TyKind, UintTy},
};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{
    AdtDestructor, Arity, BackendInterpretationPair, CastType, CompType, DomainAxiomData,
    DomainIdnSnap, FunctionIdn, Type,
};

use crate::encoders::Pure;

use super::{
    RustTy, ViperTyDatas,
    data::*,
    generics::{GenericParams, GenericParamsEnc},
    interpretation::float::FloatDomain,
    rust_ty::RustBuiltinData,
};

pub(super) type PureTyDatas = ViperTyDatas<Pure>;

impl<'vir> TyDatas<'vir> for PureTyDatas {
    type TyData = TyPureRef<'vir>;
    type OpaqueData = TyPureOpaqueData<'vir>;
    type ArrayData = TyPureArrayData<'vir>;
    type PrimitiveData = TyPurePrimData<'vir>;
    type ImmRefData = TyPureImmRefData<'vir>;
    type MutRefData = TyPureMutRefData<'vir>;
    type RawData = TyPureRawData<'vir>;
    type FieldData = TyPureFieldData<'vir>;
    type StructData = TyPureStructData<'vir>;
    type VariantData = TyPureVariantData<'vir>;
    type EnumData = TyPureEnumData<'vir>;
    type BuiltinData = TyPureBuiltinData;
}

pub type TyPure<'vir> = Ty<'vir, PureTyDatas>;
pub type TyPureParam<'vir> = <PureTyDatas as TyDatas<'vir>>::ParamData;
pub type TyPureOpaque<'vir> = <PureTyDatas as TyDatas<'vir>>::OpaqueData;
pub type TyPurePrimitive<'vir> = <PureTyDatas as TyDatas<'vir>>::PrimitiveData;
pub type TyPureImmRef<'vir> = <PureTyDatas as TyDatas<'vir>>::ImmRefData;
pub type TyPureMutRef<'vir> = <PureTyDatas as TyDatas<'vir>>::MutRefData;
pub type TyPureRaw<'vir> = <PureTyDatas as TyDatas<'vir>>::RawData;
pub type TyPureBuiltin<'vir> = <PureTyDatas as TyDatas<'vir>>::BuiltinData;

#[derive(Debug, Clone, Copy)]
pub enum TyPureBuiltinData {
    Int,
    Real,
    Set,
    Multiset,
    Seq,
    Map,
}

#[derive(Debug, Clone, Copy)]
pub struct TyPureOpaqueData<'vir> {
    /// Some arbitrary value of this type. Should probably be removed
    /// eventually, but used for now in e.g. the str-const encoding.
    pub arbitrary: FunctionIdn<'vir, (), vir::CSnap>,
}

/// Pure data for a raw pointer. Modelled like a reference (`TyPureImmRefData`)
/// but with the pointee left opaque: the snapshot carries the address and the
/// pointer metadata, and there is no `value_access` into the pointee.
#[derive(Debug, Clone, Copy)]
pub struct TyPureRawData<'vir> {
    /// Construct the snapshot from an address and pointer metadata.
    pub(super) prim_to_snap: FunctionIdn<'vir, (vir::Ref, vir::PSnap), vir::CSnap>,
    /// Function to access the pointer address.
    #[allow(dead_code)]
    pub(super) address_access: AdtDestructor<'vir, vir::CSnap, vir::Ref>,
    /// Function to access the pointer metadata (fat pointer).
    pub(super) metadata_access: AdtDestructor<'vir, vir::CSnap, vir::PSnap>,
}

#[derive(Debug, Clone, Copy)]
pub struct TyPureArrayData<'vir> {
    /// Function to access the value at the given index.
    pub(super) index_access: FunctionIdn<'vir, (vir::CSnap, vir::Int), vir::PSnap>,
    /// Function to access the ref at the given index.
    pub ref_to_index_ref: vir::FunctionIdn<'vir, (vir::Ref, vir::Int, vir::ManyTyVal), vir::Ref>,
}

#[derive(Debug, Clone, Copy)]
pub struct TyPurePrimData<'vir> {
    pub kind: TyPurePrimDataKind<'vir>,
}

#[derive(Debug, Clone, Copy)]
pub enum TyPurePrimDataKind<'vir> {
    /// Rust's `bool`, represented directly by the native Viper `Bool` type:
    /// the primitive and the snapshot coincide, so the conversions are casts.
    Bool,
    Int(TyPurePrimDataInt<'vir>),
    Float(FloatDomain<'vir>),
}

/// The integer-like primitives (`char` and the integer types), whose snapshot
/// domain wraps a Viper `Int`.
#[derive(Debug, Clone, Copy)]
pub struct TyPurePrimDataInt<'vir> {
    /// Viper primitive value as argument. Returns domain.
    pub prim_to_snap: FunctionIdn<'vir, vir::Prim, vir::CSnap>,
    /// Snapshot of self as argument. Returns Viper primitive value.
    pub snap_to_prim: FunctionIdn<'vir, vir::CSnap, vir::Prim>,
}

impl<'vir> TyPurePrimData<'vir> {
    /// The Viper primitive representation of this type (the argument of
    /// [`Self::prim_to_snap`]; for floats the raw bits).
    pub fn prim_type(&self) -> vir::TypePrim<'vir> {
        match &self.kind {
            TyPurePrimDataKind::Bool => vir::TYPE_BOOL.upcast_ty(),
            TyPurePrimDataKind::Int(_) | TyPurePrimDataKind::Float(_) => vir::TYPE_INT.upcast_ty(),
        }
    }

    /// Constructs the snapshot from the Viper primitive value.
    pub fn prim_to_snap<Curr: 'vir, Next: 'vir>(
        &self,
        prim: vir::ExprGenPrim<'vir, Curr, Next>,
    ) -> vir::ExprGenCSnap<'vir, Curr, Next> {
        match &self.kind {
            TyPurePrimDataKind::Bool => prim.downcast_ty::<vir::Bool>().upcast_ty(),
            TyPurePrimDataKind::Int(int) => int.prim_to_snap.call()(prim),
            TyPurePrimDataKind::Float(float) => float.prim_to_snap.call()(prim),
        }
    }

    /// Extracts the Viper primitive value from the snapshot.
    pub fn snap_to_prim<Curr: 'vir, Next: 'vir>(
        &self,
        snap: vir::ExprGenCSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenPrim<'vir, Curr, Next> {
        match &self.kind {
            TyPurePrimDataKind::Bool => snap.downcast_ty::<vir::Bool>().upcast_ty(),
            TyPurePrimDataKind::Int(int) => int.snap_to_prim.call()(snap),
            TyPurePrimDataKind::Float(_) => panic!("float snapshots have no primitive value"),
        }
    }
}

impl<'vir, D: TyDatas<'vir, PrimitiveData = TyPurePrimData<'vir>>> TyData<'vir, D> {
    pub fn expect_float(&self) -> &FloatDomain<'vir> {
        match &self.expect_primitive().kind {
            TyPurePrimDataKind::Float(fl) => fl,
            _ => panic!(),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct TyPureImmRefData<'vir> {
    /// Construct domain from a `Ref` value.
    pub(super) prim_to_snap: FunctionIdn<'vir, (vir::Ref, vir::PSnap, vir::PSnap), vir::CSnap>,
    /// Function to access the referee.
    pub(super) deref_access: AdtDestructor<'vir, vir::CSnap, vir::Ref>,
    /// Function to access the reference metadata (fat pointer).
    pub(super) metadata_access: AdtDestructor<'vir, vir::CSnap, vir::PSnap>,
    /// Function to access the snapshot value.
    pub(super) value_access: AdtDestructor<'vir, vir::CSnap, vir::PSnap>,
}

#[derive(Debug, Clone, Copy)]
pub struct TyPureMutRefData<'vir> {
    /// Construct domain from a `Ref` value.
    pub(super) prim_to_snap: FunctionIdn<'vir, (vir::Ref, vir::PSnap, vir::PSnap), vir::CSnap>,
    /// Function to access the referee.
    pub(super) deref_access: AdtDestructor<'vir, vir::CSnap, vir::Ref>,
    /// Function to access the reference metadata (fat pointer).
    pub(super) metadata_access: AdtDestructor<'vir, vir::CSnap, vir::PSnap>,
    /// Function to access the value (beware that this may not be set).
    pub(super) value_access: AdtDestructor<'vir, vir::CSnap, vir::PSnap>,
}

#[derive(Debug, Clone, Copy)]
pub struct TyPureStructData<'vir> {
    /// Construct domain from snapshots of fields or for primitive types
    /// from the single Viper primitive value.
    pub(super) field_snaps_to_snap: FunctionIdn<'vir, vir::ManySnap, vir::CSnap>,
}

#[derive(Debug, Clone, Copy)]
pub struct TyPureFieldData<'vir> {
    pub(super) read: AdtDestructor<'vir, vir::CSnap, vir::Snap>,
    pub(super) ref_to_field_ref:
        FunctionIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::ManyCSnap), vir::Ref>,
}

#[derive(Debug, Clone, Copy)]
pub struct TyPureEnumData<'vir> {
    #[allow(dead_code)]
    pub(super) discr_ty: vir::TypeSnap<'vir>,
    #[allow(dead_code)]
    pub(super) discr_prim: TyPurePrimitive<'vir>,
    pub(super) snap_to_discr_snap: FunctionIdn<'vir, vir::CSnap, vir::CSnap>,
}

#[derive(Debug, Clone, Copy)]
pub struct TyPureVariantData<'vir> {
    pub discr: vir::ExprCSnap<'vir>,
}

/// You probably never want to use this, use `TyUsePureEnc` instead.
/// Note: there should never be a dependency on `TyImpureEnc` inside this
/// encoder!
pub(super) type TyPureEnc = super::TyEnc<Pure>;

#[derive(Debug, Clone, Copy)]
pub struct TyPureRef<'vir> {
    pub snapshot: vir::TypeSnap<'vir>,
    pub unreachable_to_snap: FunctionIdn<'vir, (vir::ManyTyVal, vir::ManyCSnap), vir::Snap>,
}

impl<'vir> task_encoder::OutputRefAny for TyPureRef<'vir> {}

#[derive(Debug, Clone, Copy)]
pub struct TyPureEncLocal<'vir> {
    unreachable_to_snap: vir::Function<'vir>,
    /// Other functions related to this type.
    functions: &'vir [vir::Function<'vir>],
    kind: TyPureEncLocalKind<'vir>,
}

#[derive(Debug, Clone, Copy)]
pub enum TyPureEncLocalKind<'vir> {
    Domain {
        domain: vir::Domain<'vir>,
    },
    Adt {
        adt: vir::Adt<'vir>,
        discr_fn: Option<vir::Function<'vir>>,
    },
    None,
}

#[derive(Debug, Clone, Copy)]
pub enum TyPureEncError {}

impl TaskEncoder for TyPureEnc {
    task_encoder::encoder_cache!(TyPureEnc);
    const ENCODER_NAME: &'static str = "type pure encoder";
    type TaskDescription<'vir> = RustTy<'vir>;

    type OutputRef<'vir> = TyPureRef<'vir>;
    type OutputFullDependency<'vir> = TyPure<'vir>;

    /// A domain is not encoded here for Param types, the relevant domains are
    /// encoded in [`GenericEnc`]. The reason we do not encode the domain for
    /// `Param` types here is because we don't want [`GenericEnc`] to depend on
    /// this encoder: doing so would create a cyclic dependency.
    type OutputFullLocal<'vir> = Option<TyPureEncLocal<'vir>>;

    type EncodingError = TyPureEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let mut builder = TyPureBuilder::new(deps, vcx, task_key);
            let output_ref = builder.output_ref();
            deps.emit_output_ref(*task_key, output_ref)?;

            let specifics = match &task_key.specifics {
                TySpecifics::Param(param) => {
                    let builder = builder.set_domain_builder();
                    TySpecifics::Param(super::kinds::param::ty_pure(param, deps, builder)?)
                }
                TySpecifics::Opaque(opaque) => {
                    let builder = builder.set_domain_builder();
                    TySpecifics::Opaque(super::kinds::opaque::ty_pure(opaque, deps, builder)?)
                }
                TySpecifics::ArrayLike(array) => {
                    let builder = builder.set_domain_builder();
                    TySpecifics::ArrayLike(super::kinds::arraylike::ty_pure(array, deps, builder)?)
                }
                TySpecifics::Primitive(prim) => TySpecifics::Primitive(
                    super::kinds::primitive::ty_pure(vcx, prim, deps, &mut builder)?,
                ),
                TySpecifics::ImmRef(immref) => {
                    let builder = builder.set_adt_builder();
                    TySpecifics::ImmRef(super::kinds::immref::ty_pure(
                        task_key, immref, deps, builder,
                    )?)
                }
                TySpecifics::MutRef(mutref) => {
                    let builder = builder.set_adt_builder();
                    TySpecifics::MutRef(super::kinds::mutref::ty_pure(
                        task_key, mutref, deps, builder,
                    )?)
                }
                TySpecifics::Raw(raw) => {
                    let builder = builder.set_adt_builder();
                    TySpecifics::Raw(super::kinds::raw::ty_pure(task_key, raw, deps, builder)?)
                }
                TySpecifics::StructLike(structlike) => {
                    let builder = builder.set_adt_builder();
                    TySpecifics::StructLike(super::kinds::structlike::ty_pure(
                        task_key, structlike, deps, builder,
                    )?)
                }
                TySpecifics::EnumLike(enumlike) => {
                    let builder = builder.set_adt_builder();
                    TySpecifics::EnumLike(super::kinds::enumlike::ty_pure(
                        task_key, enumlike, deps, builder,
                    )?)
                }
                TySpecifics::Builtin(builtin) => {
                    TySpecifics::Builtin(super::kinds::builtin::ty_pure(builtin, &mut builder)?)
                }
            };
            let output = TyData::new(output_ref, specifics).alloc();
            Ok((Some(builder.build()), output))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors(program) {
            let Some(output) = output else {
                continue;
            };
            program.add_function(output.unreachable_to_snap);
            for function in output.functions {
                program.add_function(function);
            }
            match output.kind {
                TyPureEncLocalKind::Domain { domain } => program.add_domain(domain),
                TyPureEncLocalKind::Adt { adt, discr_fn } => {
                    program.add_adt(adt);
                    if let Some(discr_fn) = discr_fn {
                        program.add_function(discr_fn);
                    }
                }
                TyPureEncLocalKind::None => {}
            }
        }
    }
}

#[repr(transparent)]
pub(crate) struct DomainBuilder<'vir>(TyPureBuilder<'vir>);

impl<'vir> DomainBuilder<'vir> {
    pub(crate) fn data(&mut self) -> &mut DomainBuilderData<'vir> {
        match &mut self.0.data {
            BuilderData::Domain(data) => data,
            _ => panic!("not a Domain builder"),
        }
    }
}

impl<'vir> Deref for DomainBuilder<'vir> {
    type Target = TyPureBuilder<'vir>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[repr(transparent)]
pub(crate) struct AdtBuilder<'vir>(TyPureBuilder<'vir>);

impl<'vir> AdtBuilder<'vir> {
    pub(crate) fn data(&mut self) -> &mut AdtBuilderData<'vir> {
        match &mut self.0.data {
            BuilderData::Adt(data) => data,
            _ => panic!("not an ADT builder"),
        }
    }
}

impl<'vir> Deref for AdtBuilder<'vir> {
    type Target = TyPureBuilder<'vir>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

pub(crate) struct TyPureBuilder<'vir> {
    pub(crate) vcx: &'vir vir::VirCtxt<'vir>,
    name: vir::ViperIdent<'vir>,
    self_type: vir::TypeSnap<'vir>,
    unreachable_to_snap: FunctionIdn<'vir, (vir::ManyTyVal, vir::ManyCSnap), vir::Snap>,
    pub(super) params: GenericParams<'vir>,
    data: BuilderData<'vir>,
}

pub enum BuilderData<'vir> {
    Adt(AdtBuilderData<'vir>),
    Domain(DomainBuilderData<'vir>),
    None,
}

#[derive(Default)]
pub(crate) struct AdtBuilderData<'vir> {
    constructors: Vec<vir::AdtConstructor<'vir>>,
    discr_fn: Option<DiscrFnBuilder<'vir>>,
    /// Other related functions (for example Ref field accessors).
    functions: Vec<vir::Function<'vir>>,
}

#[derive(Default)]
pub(crate) struct DomainBuilderData<'vir> {
    axioms: Vec<vir::DomainAxiom<'vir>>,
    functions: Vec<vir::DomainFunction<'vir>>,
    interpretation: Option<&'vir [&'vir BackendInterpretationPair<'vir>]>,
}

#[derive(Clone, Copy)]
enum DiscrFnBuilder<'vir> {
    Building {
        param: vir::LocalDeclCSnap<'vir>,
        recv: vir::ExprCSnap<'vir>,
        acc: vir::ExprCSnap<'vir>,
    },
    Built(vir::Function<'vir>),
}

impl<'vir> TyPureBuilder<'vir> {
    pub(crate) fn new<E: TaskEncoder>(
        deps: &mut TaskEncoderDependencies<'vir, E>,
        vcx: &'vir vir::VirCtxt<'vir>,
        ty: RustTy<'vir>,
    ) -> Self {
        let params = deps.require_dep::<GenericParamsEnc>(ty.params).unwrap();
        let name = vir::ViperIdent::new(vir::vir_format!(vcx, "s_{}", ty.name()));
        // The `Int`/`Real` builtins and Rust's `bool` are represented directly
        // by the native Viper `Int`/`Perm`/`Bool` types; nothing is emitted
        // for them.
        let self_type = match &ty.specifics {
            TySpecifics::Builtin(RustBuiltinData::Int) => vir::TYPE_INT.upcast_ty(),
            TySpecifics::Builtin(RustBuiltinData::Real) => vir::TYPE_PERM.upcast_ty(),
            // The collection builtins are encoded at their most generic
            // instantiation, so the elements are generic snapshots.
            TySpecifics::Builtin(RustBuiltinData::Set(inner)) => {
                assert!(inner.decompose(ty.params).ty.specifics.is_param());
                vcx.mk_ty_set(vir::TYPE_PSNAP).upcast_ty()
            }
            TySpecifics::Builtin(RustBuiltinData::Multiset(inner)) => {
                assert!(inner.decompose(ty.params).ty.specifics.is_param());
                vcx.mk_ty_multiset(vir::TYPE_PSNAP).upcast_ty()
            }
            TySpecifics::Builtin(RustBuiltinData::Seq(inner)) => {
                assert!(inner.decompose(ty.params).ty.specifics.is_param());
                vcx.mk_ty_seq(vir::TYPE_PSNAP).upcast_ty()
            }
            TySpecifics::Builtin(RustBuiltinData::Map(inner1, inner2)) => {
                assert!(inner1.decompose(ty.params).ty.specifics.is_param());
                assert!(inner2.decompose(ty.params).ty.specifics.is_param());
                vcx.mk_ty_map(vir::TYPE_PSNAP, vir::TYPE_PSNAP).upcast_ty()
            }
            TySpecifics::Primitive(prim) if prim.is_bool() => vir::TYPE_BOOL.upcast_ty(),
            _ => DomainIdnSnap::new(name, 0)(),
        };
        let unreachable_to_snap = FunctionIdn::new(
            vir::ViperIdent::new(vir::vir_format!(vcx, "{name}_unreachable")),
            (params.ty_args(), params.const_args()),
            self_type,
        );
        TyPureBuilder {
            vcx,
            name,
            self_type,
            unreachable_to_snap,
            params,
            data: BuilderData::None,
        }
    }

    pub(crate) fn self_type(&self) -> vir::TypeCSnap<'vir> {
        self.self_type.downcast_ty()
    }

    pub(crate) fn output_ref(&self) -> TyPureRef<'vir> {
        TyPureRef {
            snapshot: self.self_type,
            unreachable_to_snap: self.unreachable_to_snap,
        }
    }

    pub(crate) fn set_domain_builder(&mut self) -> &mut DomainBuilder<'vir> {
        match &mut self.data {
            BuilderData::Adt(_) => panic!("already an ADT builder"),
            BuilderData::Domain(_) => {}
            data @ BuilderData::None => {
                *data = BuilderData::Domain(DomainBuilderData::default());
            }
        }
        // SAFETY: `DomainBuilder` is repr transparent
        let builder = self as *mut Self as *mut DomainBuilder<'vir>;
        unsafe { &mut *builder }
    }

    pub(crate) fn set_adt_builder(&mut self) -> &mut AdtBuilder<'vir> {
        match &mut self.data {
            BuilderData::Domain(_) => panic!("already a Domain builder"),
            BuilderData::Adt(_) => {}
            data @ BuilderData::None => {
                *data = BuilderData::Adt(AdtBuilderData::default());
            }
        }
        // SAFETY: `AdtBuilder` is repr transparent
        let builder = self as *mut Self as *mut AdtBuilder<'vir>;
        unsafe { &mut *builder }
    }

    pub(crate) fn build(self) -> TyPureEncLocal<'vir> {
        vir::with_vcx(|vcx| {
            let unreachable_to_snap = vcx.mk_function(
                self.unreachable_to_snap,
                (self.params.ty_decls(), self.params.const_decls()),
                &[],
                vcx.alloc_array(&[vcx.mk_bool::<false>()]),
                None,
                None,
            );
            let functions = match &self.data {
                BuilderData::Adt(data) => data.functions.as_slice(),
                _ => &[],
            };
            let functions = vcx.alloc_slice(functions);
            let kind = self.build_kind();
            TyPureEncLocal {
                unreachable_to_snap,
                kind,
                functions,
            }
        })
    }

    fn build_kind(self) -> TyPureEncLocalKind<'vir> {
        match self.data {
            BuilderData::Domain(data) => {
                let domain = self.vcx.mk_domain(
                    self.name,
                    &[],
                    self.vcx.alloc_slice(data.axioms.as_slice()),
                    self.vcx.alloc_slice(data.functions.as_slice()),
                    data.interpretation,
                );
                TyPureEncLocalKind::Domain { domain }
            }
            BuilderData::Adt(data) => {
                let adt = self.vcx.mk_adt(
                    self.name,
                    &[],
                    self.vcx.alloc_slice(data.constructors.as_slice()),
                );
                let discr_fn = data.discr_fn.map(|df| {
                    let DiscrFnBuilder::Built(df) = df else {
                        panic!("discriminant function not built");
                    };
                    df
                });
                TyPureEncLocalKind::Adt { adt, discr_fn }
            }
            // Natively-represented types (`Int`/`Real`/`bool`) emit nothing.
            BuilderData::None => TyPureEncLocalKind::None,
        }
    }
}

impl<'vir> AdtBuilder<'vir> {
    pub(crate) fn constructor<A: vir::Arity>(
        &mut self,
        prefix: &str,
        fields: A::Tys<'vir>,
        discr: Option<vir::ExprCSnap<'vir>>,
    ) -> (
        FunctionIdn<'vir, A, vir::CSnap>,
        Vec<vir::AdtDestructor<'vir, vir::CSnap, vir::Dyn>>,
    ) {
        let name = format!("{prefix}cons");
        let self_ty = self.self_type();
        assert!(
            self.data().discr_fn.is_none() || discr.is_some(),
            "discr was passed previously, but now it wasn't"
        );
        let self_name = self.name;
        let name = vir::vir_format!(self.vcx, "{self_name}_{name}",);
        let locals = self.vcx.alloc_slice(
            &A::params(fields)
                .into_iter()
                .enumerate()
                .map(|(i, ty)| {
                    self.vcx
                        .mk_local_decl(vir::vir_format!(self.vcx, "{self_name}_{prefix}{i}",), ty)
                })
                .collect::<Vec<_>>(),
        );
        let constructor = self.vcx.mk_adt_constructor(name, locals);
        self.data().constructors.push(constructor);
        let ident = FunctionIdn::new(vir::ViperIdent::new(name), fields, self_ty);
        if let Some(discr) = discr {
            let df = self.data().discr_fn.take().map(|df| {
                let DiscrFnBuilder::Building { param, recv, acc } = df else {
                    panic!("discriminant function was already built");
                };
                let acc = self.vcx.mk_ternary_expr(
                    self.vcx.mk_adt_discriminator_expr(recv, name),
                    discr,
                    acc,
                );
                DiscrFnBuilder::Building { param, recv, acc }
            });
            let df = df.unwrap_or_else(|| {
                let param = self.vcx.mk_local_decl("self", self_ty);
                DiscrFnBuilder::Building {
                    param,
                    recv: self.vcx.mk_local_ex(param),
                    acc: discr,
                }
            });
            self.data().discr_fn = Some(df)
        }
        (
            ident,
            locals
                .iter()
                .map(|arg| self.vcx.mk_adt_destructor(arg.name, self_ty, arg.ty))
                .collect(),
        )
    }

    pub(crate) fn build_discr_fn(
        &mut self,
        ty: vir::TypeCSnap<'vir>,
    ) -> vir::FunctionIdn<'vir, vir::CSnap, vir::CSnap> {
        let self_ty = self.self_type();
        let param = self.vcx.mk_local_decl("self", self_ty);
        let ident = FunctionIdn::new(
            vir::ViperIdent::new(vir::vir_format!(self.vcx, "{}_discr", self.name)),
            param.ty,
            ty,
        );
        let (expr, posts) = if let Some(df) = self.data().discr_fn {
            let DiscrFnBuilder::Building { acc, .. } = df else {
                panic!("discriminant function already built");
            };
            (Some(acc), &[][..])
        } else {
            // We get here if we didn't add any constructors to the ADT (i.e.
            // this is an empty enum = uninhabitable type). Viper forbids this
            // (see silver#693, silver#696), so here we will just add a dummy
            // constructor that won't actually be used by the encoders. Instead
            // we encode the uninhabitability by adding an `ensures false` to
            // the discriminant function.
            // TODO: https://github.com/Aurel300/prusti-dev/pull/89#discussion_r2263306839
            let self_name = self.name;
            let name = vir::vir_format!(self.vcx, "{self_name}_DummyConstructor",);
            let constructor = self.vcx.mk_adt_constructor::<(), !, vir::Dyn>(name, &[]);
            self.data().constructors.push(constructor);
            (None, self.vcx.alloc_slice(&[self.vcx.mk_bool::<false>()]))
        };
        let built_fn = self
            .vcx
            .mk_function(ident, (param,), &[], posts, None, expr);
        self.data().discr_fn = Some(DiscrFnBuilder::Built(built_fn));
        ident
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn function<A: Arity, T: CompType>(
        &mut self,
        name: &str,
        args: A::Tys<'vir>,
        ret: vir::Type<'vir, T>,
        params: A::Locals<'_, 'vir>,
        pres: &[vir::ExprBool<'vir>],
        posts: &[vir::ExprBool<'vir>],
        expr: Option<vir::Expr<'vir, T>>,
    ) -> FunctionIdn<'vir, A, T> {
        let name = vir::vir_format!(self.vcx, "{}_{name}", self.name);
        let ident = FunctionIdn::new(vir::ViperIdent::new(name), args, ret);
        let function = self.vcx.mk_function(
            ident,
            params,
            self.vcx.alloc_slice(pres),
            self.vcx.alloc_slice(posts),
            None,
            expr,
        );
        self.data().functions.push(function);
        ident
    }
}

impl<'vir> DomainBuilder<'vir> {
    pub(crate) fn function<A: Arity, T: CompType>(
        &mut self,
        name: &str,
        args: A::Tys<'vir>,
        ret: Type<'vir, T>,
    ) -> FunctionIdn<'vir, A, T> {
        let name = vir::vir_format!(self.vcx, "{}_{name}", self.name);
        let ident = FunctionIdn::new(vir::ViperIdent::new(name), args, ret);
        let function = self.vcx.mk_domain_function(ident, false, None);
        self.data().functions.push(function);
        ident
    }

    pub(crate) fn backend_func<A: Arity, T: CompType>(
        &mut self,
        name: &str,
        args: A::Tys<'vir>,
        ret: Type<'vir, T>,
        interpretation: Option<&'static str>,
    ) -> FunctionIdn<'vir, A, T> {
        let name = vir::vir_format!(self.vcx, "{}_{name}", self.name);
        let ident = FunctionIdn::new(vir::ViperIdent::new(name), args, ret);
        let function = self.vcx.mk_domain_function(ident, false, interpretation);
        self.data().functions.push(function);
        ident
    }

    pub(crate) fn axiom(&mut self, name: &str, expr: vir::ExprBool<'vir>) {
        let name = vir::vir_format!(self.vcx, "{}_ax_{name}", self.name);
        let axiom = self.vcx.alloc(DomainAxiomData { name, expr });
        self.data().axioms.push(axiom);
    }

    pub(crate) fn set_interpretation(
        &mut self,
        interp: &'vir [&'vir BackendInterpretationPair<'vir>],
    ) {
        self.data().interpretation = Some(interp);
    }
}

impl<'vir> TyPurePrimData<'vir> {
    pub fn expr_from_bits(&self, ty: ty::Ty<'vir>, value: u128) -> vir::ExprPrim<'vir> {
        match &self.kind {
            TyPurePrimDataKind::Bool => {
                vir::with_vcx(|vcx| vcx.mk_const_expr(vir::ConstData::Bool(value != 0)))
            }
            TyPurePrimDataKind::Int(_) | TyPurePrimDataKind::Float(_) => {
                let (bit_width, signed) = match ty.kind() {
                    TyKind::Int(IntTy::Isize) => ((std::mem::size_of::<isize>() * 8) as u64, true),
                    TyKind::Int(ty) => (ty.bit_width().unwrap(), true),
                    TyKind::Uint(UintTy::Usize) => {
                        ((std::mem::size_of::<usize>() * 8) as u64, false)
                    }
                    TyKind::Uint(ty) => (ty.bit_width().unwrap(), false),
                    TyKind::Char => (32, false),
                    // The float prim_to_snap takes the raw bits as an unsigned integer.
                    TyKind::Float(..) => (0, false),
                    kind => unreachable!("{kind:?}"),
                };
                let size = abi::Size::from_bits(bit_width);
                let negative_value = if signed {
                    let value = size.sign_extend(value);
                    Some(value).filter(|value| value.is_negative())
                } else {
                    None
                };
                match negative_value {
                    Some(value) => vir::with_vcx(|vcx| {
                        let value = vcx.mk_const_expr(vir::ConstData::Int(value.unsigned_abs()));
                        vcx.mk_unary_op_expr(vir::UnOpKind::Neg, value)
                    }),
                    None => vir::with_vcx(|vcx| vcx.mk_const_expr(vir::ConstData::Int(value))),
                }
            }
        }
    }
}
