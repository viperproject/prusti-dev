// TODO: this lint is something we should fix; to address there should probably
//   be an indirection in error storage somewhere, maybe even in `task-encoder`?
#![allow(clippy::result_large_err)]

use std::ops::Deref;

use prusti_rustc_interface::{
    middle::ty::{self, IntTy, ParamTy, TyKind, UintTy},
    span::symbol,
    abi,
};
use task_encoder::{EncodeFullError, EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{
    AdtDestructor, Arity, CallableIdn, CastType, CompType, DomainAxiomData, DomainIdnCSnap, FunctionIdn, Type
};

use super::{
    most_generic_ty::{extract_type_params, get_vir_base_name_kind, MostGenericTy},
    rust_ty_snapshots::RustTySnapshotsEnc,
};

/// You probably never want to use this, use `SnapshotEnc` instead.
/// Note: there should never be a dependency on `PredicateEnc` inside this
/// encoder!
pub struct DomainEnc;

#[derive(Clone, Copy, Debug)]
pub struct DomainDataPrim<'vir> {
    pub prim_type: vir::TypePrim<'vir>,
    /// Snapshot of self as argument. Returns Viper primitive value.
    pub snap_to_prim: FunctionIdn<'vir, vir::CSnap, vir::Prim>,
    /// Viper primitive value as argument. Returns domain.
    pub prim_to_snap: FunctionIdn<'vir, vir::Prim, vir::CSnap>,
}
#[derive(Clone, Copy, Debug)]
pub struct DomainDataImmRef<'vir> {
    /// Construct domain from a `Ref` value.
    pub prim_to_snap: FunctionIdn<'vir, (vir::Ref, vir::PSnap), vir::CSnap>,
    /// Function to access the referee.
    pub deref_access: AdtDestructor<'vir, vir::CSnap, vir::Ref>,
    /// Function to access the snapshot value.
    pub value_access: AdtDestructor<'vir, vir::CSnap, vir::PSnap>,
}
#[derive(Clone, Copy, Debug)]
pub struct DomainDataMutRef<'vir> {
    /// Construct domain from a `Ref` value.
    pub prim_to_snap: FunctionIdn<'vir, (vir::Ref, vir::PSnap), vir::CSnap>,
    /// Function to access the referee.
    pub deref_access: AdtDestructor<'vir, vir::CSnap, vir::Ref>,
    /// Function to access the snapshot value.
    pub value_access: AdtDestructor<'vir, vir::CSnap, vir::PSnap>,
}
#[derive(Clone, Copy, Debug)]
pub struct DomainDataStruct<'vir> {
    /// Construct domain from snapshots of fields or for primitive types
    /// from the single Viper primitive value.
    pub field_snaps_to_snap: FunctionIdn<'vir, vir::ManySnap, vir::CSnap>,
    /// Functions to access the fields.
    pub field_access: &'vir [AdtDestructor<'vir, vir::CSnap, vir::Snap>],
}
#[derive(Clone, Copy, Debug)]
pub struct DomainDataEnum<'vir> {
    pub discr_ty: vir::TypeSnap<'vir>,
    pub discr_prim: DomainDataPrim<'vir>,
    //pub discr_bounds: DiscrBounds<'vir>,
    pub snap_to_discr_snap: FunctionIdn<'vir, vir::CSnap, vir::CSnap>,
    pub variants: &'vir [DomainDataVariant<'vir>],
}
#[derive(Clone, Copy, Debug)]
pub struct DomainDataVariant<'vir> {
    pub name: symbol::Symbol,
    pub vid: abi::VariantIdx,
    pub discr: vir::ExprCSnap<'vir>,
    pub fields: DomainDataStruct<'vir>,
}

#[derive(Clone, Copy, Debug)]
pub enum DiscrBounds<'vir> {
    Range {
        lower: vir::ExprInt<'vir>,
        upper: vir::ExprInt<'vir>,
    },
    Explicit(&'vir [vir::ExprInt<'vir>]),
}

#[derive(Clone, Copy, Debug)]
pub enum DomainEncSpecifics<'vir> {
    Opaque,
    Param,
    Never,
    Primitive(DomainDataPrim<'vir>),
    ImmRef(DomainDataImmRef<'vir>),
    MutRef(DomainDataMutRef<'vir>),
    // structs, tuples
    StructLike(DomainDataStruct<'vir>),
    EnumLike(Option<DomainDataEnum<'vir>>),
}

#[derive(Clone, Debug)]
pub struct DomainEncOutputRef<'vir> {
    pub base_name: String,
    pub domain: vir::DomainIdnSnap<'vir>,
}

impl<'vir> task_encoder::OutputRefAny for DomainEncOutputRef<'vir> {}

pub fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
    for output in DomainEnc::all_outputs_local() {
        match output {
            DomainEncOutput::Domain(domain) => program.add_domain(domain),
            DomainEncOutput::Adt { adt, discr_fn } => {
                program.add_adt(adt);
                if let Some(discr_fn) = discr_fn {
                    program.add_function(discr_fn);
                }
            }
            DomainEncOutput::None => {}
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum DomainEncOutput<'vir> {
    None,
    Domain(vir::Domain<'vir>),
    Adt {
        adt: vir::Adt<'vir>,
        discr_fn: Option<vir::Function<'vir>>,
    },
}

impl TaskEncoder for DomainEnc {
    task_encoder::encoder_cache!(DomainEnc);

    type TaskDescription<'vir> = MostGenericTy<'vir>;

    type OutputRef<'vir> = DomainEncOutputRef<'vir>;
    type OutputFullDependency<'vir> = DomainEncSpecifics<'vir>;

    /// A domain is not encoded here for Param types, the relevant domains are
    /// encoded in [`GenericEnc`]. The reason we do not encode the domain for
    /// `Param` types here is because we don't want [`GenericEnc`] to depend on
    /// this encoder: doing so would create a cyclic dependency.
    type OutputFullLocal<'vir> = DomainEncOutput<'vir>;

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let mut builder = PureTypeCommon::new(vcx);

            if matches!(task_key.kind(), TyKind::Param(_)) {
                let (specifics, builder) = super::kinds::param::domain(*task_key, deps, builder)?;
                return Ok((PureTypeCommon::build(builder), specifics));
            }

            let base_name = get_vir_base_name_kind(task_key.kind(), builder.vcx);
            builder.set_name(&base_name);
            let output_ref = builder.output_ref(base_name);
            deps.emit_output_ref(*task_key, output_ref.clone())?;

            let (specifics, builder) = match task_key.kind() {
                TyKind::Bool
                | TyKind::Char
                | TyKind::Int(_)
                | TyKind::Uint(_)
                | TyKind::Float(_) => {
                    super::kinds::primitive::domain(*task_key, deps, builder)?
                }
                TyKind::Closure(..) => {
                    super::kinds::closure::domain(*task_key, &output_ref, deps, builder)?
                }
                TyKind::Adt(..) => {
                    super::kinds::adt::domain(*task_key, &output_ref, deps, builder)?
                }
                TyKind::Tuple(..) => {
                    super::kinds::tuple::domain(*task_key, &output_ref, deps, builder)?
                }
                TyKind::Never => super::kinds::never::domain(*task_key, deps, builder)?,
                TyKind::Ref(_, _, ty::Mutability::Not) => {
                    super::kinds::immref::domain(*task_key, &output_ref, deps, builder)?
                }
                TyKind::Ref(_, _, ty::Mutability::Mut) => {
                    super::kinds::mutref::domain(*task_key, deps, builder)?
                }
                TyKind::Param(_) => super::kinds::param::domain(*task_key, deps, builder)?,
                TyKind::Str => super::kinds::str::domain(*task_key, deps, builder)?,
                _kind => super::kinds::opaque::domain(*task_key, deps, builder)?,
            };
            Ok((PureTypeCommon::build(builder), specifics))
        })
    }
}

pub(crate) struct PureTypeCommon<'vir> {
    pub(crate) vcx: &'vir vir::VirCtxt<'vir>,
    name: Option<&'vir str>,
    generics: Option<Vec<vir::LocalDeclTyVal<'vir>>>,
    domain_ident: Option<vir::DomainIdnCSnap<'vir>>,
    self_type: Option<vir::TypeCSnap<'vir>>,
}

pub(crate) struct DomainBuilder<'vir> {
    axioms: Vec<vir::DomainAxiom<'vir>>,
    functions: Vec<vir::DomainFunction<'vir>>,
    inner: PureTypeCommon<'vir>,
}

impl<'vir> Deref for DomainBuilder<'vir> {
    type Target = PureTypeCommon<'vir>;
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

pub(crate) struct AdtBuilder<'vir> {
    constructors: Vec<vir::AdtConstructor<'vir>>,
    discr_fn: Option<DiscrFnBuilder<'vir>>,
    inner: PureTypeCommon<'vir>,
}

impl<'vir> Deref for AdtBuilder<'vir> {
    type Target = PureTypeCommon<'vir>;
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

pub(crate) type PureTypeBuilder<'vir> = Result<AdtBuilder<'vir>, DomainBuilder<'vir>>;

#[derive(Clone, Copy)]
enum DiscrFnBuilder<'vir> {
    Building {
        param: vir::LocalDeclCSnap<'vir>,
        recv: vir::ExprCSnap<'vir>,
        acc: vir::ExprCSnap<'vir>,
    },
    Built(vir::Function<'vir>),
}

impl<'vir> PureTypeCommon<'vir> {
    pub(crate) fn new(vcx: &'vir vir::VirCtxt<'vir>) -> Self {
        PureTypeCommon {
            vcx,
            name: None,
            generics: None,
            domain_ident: None,
            self_type: None,
        }
    }

    pub(crate) fn set_name(&mut self, name: &str) {
        let name = vir::vir_format!(self.vcx, "s_{name}");
        self.name = Some(name);
        let domain_ident = DomainIdnCSnap::new(vir::ViperIdent::new(name));
        self.domain_ident = Some(domain_ident);
        self.self_type = Some(domain_ident());
    }

    pub(crate) fn set_generics(&mut self, generics: Vec<vir::LocalDeclTyVal<'vir>>) {
        self.generics = Some(generics);
    }

    pub(crate) fn self_type(&self) -> vir::TypeCSnap<'vir> {
        self.self_type.expect("name should be set")
    }

    pub(crate) fn output_ref(&self, base_name: String) -> DomainEncOutputRef<'vir> {
        DomainEncOutputRef {
            base_name,
            domain: self.domain_ident.expect("name should be set").cast_ty(),
        }
    }

    pub(crate) fn build(builder: PureTypeBuilder<'vir>) -> DomainEncOutput<'vir> {
        match builder {
            Err(builder) => {
                let Some(domain_ident) = builder.domain_ident else {
                    return DomainEncOutput::None;
                };
                let domain = builder.vcx.mk_domain(
                    domain_ident.name(),
                    &[],
                    builder.vcx.alloc_slice(builder.axioms.as_slice()),
                    builder.vcx.alloc_slice(builder.functions.as_slice()),
                );
                DomainEncOutput::Domain(domain)
            }
            Ok(builder) => {
                let Some(domain_ident) = builder.domain_ident else {
                    return DomainEncOutput::None;
                };
                let adt = builder
                    .vcx
                    .mk_adt(domain_ident.name(), &[], builder.vcx.alloc_slice(builder.constructors.as_slice()));
                let discr_fn = builder.discr_fn.map(|df| {
                    let DiscrFnBuilder::Built(df) = df else {
                        panic!("discriminant function not built");
                    };
                    df
                });
                DomainEncOutput::Adt { adt, discr_fn }
            }
        }
    }
}

impl<'vir> DomainBuilder<'vir> {
    pub(crate) fn new(inner: PureTypeCommon<'vir>) -> Self {
        DomainBuilder {
            axioms: Vec::new(),
            functions: Vec::new(),
            inner,
        }
    }
}

impl<'vir> AdtBuilder<'vir> {
    pub(crate) fn new(inner: PureTypeCommon<'vir>) -> Self {
        AdtBuilder {
            constructors: Vec::new(),
            discr_fn: None,
            inner,
        }
    }

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
            self.discr_fn.is_none() || discr.is_some(),
            "discr was passed previously, but now it wasn't"
        );
        let self_name = self.name.expect("name should be set");
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
        self.constructors.push(self.vcx.mk_adt_constructor(name, locals));
        let ident = FunctionIdn::new(
            vir::ViperIdent::new(name),
            fields,
            self_ty,
        );
        if let Some(discr) = discr {
            let df = self.discr_fn.take().map(|df| {
                let DiscrFnBuilder::Building { param, recv, acc } = df else {
                    panic!("discriminant function was already built");
                };
                let acc =
                    self.vcx
                        .mk_ternary_expr(self.vcx.mk_adt_discriminator_expr(recv, name), discr, acc);
                DiscrFnBuilder::Building { param, recv, acc }
            });
            let df = df.unwrap_or_else(|| DiscrFnBuilder::Building {
                param: self.vcx.mk_local_decl("self", self_ty),
                recv: self.vcx.mk_local_ex("self", self_ty),
                acc: discr,
            });
            self.discr_fn = Some(df)
        }
        (
            ident,
            locals.iter()
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
            vir::ViperIdent::new(vir::vir_format!(
                self.vcx,
                "{}_discr",
                self.name.expect("name should be set")
            )),
            param.ty,
            ty,
        );
        let (expr, posts) = if let Some(df) = self.discr_fn {
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
            let self_name = self.name.expect("name should be set");
            let name = vir::vir_format!(self.vcx, "{self_name}_DummyConstructor",);
            self.constructors.push(self.vcx.mk_adt_constructor::<(), !, vir::Dyn>(name, &[]));
            (None, self.vcx.alloc_slice(&[self.vcx.mk_bool::<false>()]))
        };
        let built_fn = self.vcx.mk_function(
            ident,
            (param,),
            &[],
            posts,
            None,
            expr,
        );
        self.discr_fn = Some(DiscrFnBuilder::Built(built_fn));
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
        let name = vir::vir_format!(
            self.vcx,
            "{}_{name}",
            self.name.expect("name should be set")
        );
        let ident = FunctionIdn::new(vir::ViperIdent::new(name), args, ret);
        self.functions.push(self.vcx.mk_domain_function(ident, false));
        ident
    }

    pub(crate) fn axiom(&mut self, name: &str, expr: vir::ExprBool<'vir>) {
        let name = vir::vir_format!(
            self.vcx,
            "{}_ax_{name}",
            self.name.expect("name should be set")
        );
        self.axioms.push(self.vcx.alloc(DomainAxiomData { name, expr }));
    }
}

// Utility functions

impl<'vir> DomainEncSpecifics<'vir> {
    #[track_caller]
    pub fn expect_primitive(self) -> DomainDataPrim<'vir> {
        match self {
            Self::Primitive(data) => data,
            _ => panic!("expected primitive"),
        }
    }
    #[track_caller]
    pub fn expect_immref(self) -> DomainDataImmRef<'vir> {
        match self {
            Self::ImmRef(data) => data,
            _ => panic!("expected immref"),
        }
    }
    #[track_caller]
    pub fn expect_mutref(self) -> DomainDataMutRef<'vir> {
        match self {
            Self::MutRef(data) => data,
            _ => panic!("expected mutref"),
        }
    }
    #[track_caller]
    pub fn expect_structlike(self) -> DomainDataStruct<'vir> {
        match self {
            Self::StructLike(data) => data,
            _ => panic!("expected struct-like (was {self:?}"),
        }
    }
    pub fn get_enumlike(self) -> Option<Option<DomainDataEnum<'vir>>> {
        match self {
            Self::EnumLike(data) => Some(data),
            _ => None,
        }
    }
    #[track_caller]
    pub fn expect_enumlike(self) -> Option<DomainDataEnum<'vir>> {
        match self {
            Self::EnumLike(data) => data,
            _ => panic!("expected enum-like, was {self:?}"),
        }
    }
}
impl<'vir> DomainDataPrim<'vir> {
    pub fn expr_from_bits(&self, ty: ty::Ty<'vir>, value: u128) -> vir::ExprPrim<'vir> {
        match self.prim_type.kind() {
            vir::TypeKind::Bool => {
                vir::with_vcx(|vcx| vcx.mk_const_expr(vir::ConstData::Bool(value != 0)))
            }
            vir::TypeKind::Int => {
                let (bit_width, signed) = match ty.kind() {
                    TyKind::Int(IntTy::Isize) => ((std::mem::size_of::<isize>() * 8) as u64, true),
                    TyKind::Int(ty) => (ty.bit_width().unwrap(), true),
                    TyKind::Uint(UintTy::Usize) => {
                        ((std::mem::size_of::<usize>() * 8) as u64, true)
                    }
                    TyKind::Uint(ty) => (ty.bit_width().unwrap(), false),
                    TyKind::Char => (32, false),
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
            ref k => unreachable!("{k:?}"),
        }
    }
}

/// Data for encoding field access functions and axioms
#[derive(Clone)]
pub(super) struct FieldTy<'vir> {
    pub(super) rust_ty: ty::Ty<'vir>,

    /// The type of encoded field
    pub(super) ty: vir::TypeSnap<'vir>,
}

impl<'vir> FieldTy<'vir> {
    pub fn mk_field_tys<T: TaskEncoder>(
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, T>,
        variant: &ty::VariantDef,
        params: ty::GenericArgsRef<'vir>,
    ) -> Result<Vec<Self>, EncodeFullError<'vir, T>> {
        variant
            .fields
            .iter()
            .map(|f| f.ty(vcx.tcx(), params))
            .map(|ty| Self::from_ty(deps, ty))
            .collect::<Result<Vec<_>, _>>()
    }

    pub(super) fn from_ty<T: TaskEncoder>(
        deps: &mut TaskEncoderDependencies<'vir, T>,
        ty: ty::Ty<'vir>,
    ) -> Result<FieldTy<'vir>, EncodeFullError<'vir, T>> {
        let vir_ty = deps
            .require_ref::<RustTySnapshotsEnc>(ty)?
            .generic_snapshot
            .snapshot;
        Ok(FieldTy {
            rust_ty: ty,
            ty: vir_ty,
        })
    }
}
