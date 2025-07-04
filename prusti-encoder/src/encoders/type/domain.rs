// TODO: this lint is something we should fix; to address there should probably
//   be an indirection in error storage somewhere, maybe even in `task-encoder`?
#![allow(clippy::result_large_err)]

use prusti_rustc_interface::{
    middle::ty::{self, IntTy, ParamTy, TyKind, UintTy},
    span::symbol,
    target::abi,
};
use task_encoder::{EncodeFullError, EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{
    Arity, CallableIdn, CastType, CompType, DomainAxiomData, DomainIdnCSnap, FunctionIdn, Type,
};

/// You probably never want to use this, use `SnapshotEnc` instead.
/// Note: there should never be a dependency on `PredicateEnc` inside this
/// encoder!
pub struct DomainEnc;

#[derive(Clone, Copy, Debug)]
pub struct FieldFunctions<'vir> {
    /// Snapshot of self as argument. Returns domain of field.
    pub read: FunctionIdn<'vir, vir::CSnap, vir::Snap>,
    /// Snapshot of self as first argument and of field as second. Returns
    /// updated domain of self.
    pub write: FunctionIdn<'vir, (vir::CSnap, vir::Snap), vir::CSnap>,
}

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
    pub deref_access: FunctionIdn<'vir, vir::CSnap, vir::Ref>,
    /// Function to access the snapshot value.
    pub value_access: FunctionIdn<'vir, vir::CSnap, vir::PSnap>,
}
#[derive(Clone, Copy, Debug)]
pub struct DomainDataMutRef<'vir> {
    /// Construct domain from a `Ref` value.
    pub prim_to_snap: FunctionIdn<'vir, (vir::Ref, vir::PSnap), vir::CSnap>,
    /// Function to access the referee.
    pub deref_access: FunctionIdn<'vir, vir::CSnap, vir::Ref>,
    /// Function to access the snapshot value.
    pub value_access: FunctionIdn<'vir, vir::CSnap, vir::PSnap>,
}
#[derive(Clone, Copy, Debug)]
pub struct DomainDataStruct<'vir> {
    /// Construct domain from snapshots of fields or for primitive types
    /// from the single Viper primitive value.
    pub field_snaps_to_snap: FunctionIdn<'vir, vir::ManySnap, vir::CSnap>,
    /// Functions to access the fields.
    pub field_access: &'vir [FieldFunctions<'vir>],
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
    pub(super) ty_param_accessors: &'vir [FunctionIdn<'vir, vir::TyVal, vir::TyVal>],
    /// Returns the Viper representation of the type of a snapshot-encoded value
    pub typeof_function: FunctionIdn<'vir, vir::Snap, vir::TyVal>,
}

impl<'vir> DomainEncOutputRef<'vir> {
    /// Takes as input a snapshot encoding of a rust value, and returns
    /// the `idx`th type parameter of it's type.
    pub fn ty_param_from_snap(
        &self,
        _vcx: &'vir vir::VirCtxt,
        idx: usize,
        snap: vir::ExprCSnap<'vir>,
    ) -> vir::ExprTyVal<'vir> {
        (self.ty_param_accessors[idx])((self.typeof_function)(snap.upcast_ty()))
    }
}

impl<'vir> task_encoder::OutputRefAny for DomainEncOutputRef<'vir> {}

use super::{
    lifted::{
        ty::{EncodeGenericsAsParamTy, LiftedTy, LiftedTyEnc},
        ty_constructor::TyConstructorEnc,
    },
    most_generic_ty::{extract_type_params, get_vir_base_name_kind, MostGenericTy},
    rust_ty_snapshots::RustTySnapshotsEnc,
};

pub fn all_outputs<'vir>() -> Vec<vir::Domain<'vir>> {
    DomainEnc::all_outputs().into_iter().flatten().collect()
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
    type OutputFullLocal<'vir> = Option<vir::Domain<'vir>>;

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let mut builder = DomainBuilder::new(vcx);

            if matches!(task_key.kind(), TyKind::Param(_)) {
                let specifics = super::kinds::param::domain(*task_key, deps, &mut builder)?;
                return Ok((builder.build(), specifics));
            }

            let base_name = get_vir_base_name_kind(task_key.kind(), builder.vcx);
            builder.set_name(&base_name);
            let typeof_ident = builder.function("typeof", builder.self_type(), builder.type_type());
            let ty_param_accessors = deps
                .require_ref::<TyConstructorEnc>(*task_key)?
                .ty_param_accessors;
            let output_ref = builder.output_ref(base_name, typeof_ident, ty_param_accessors);
            deps.emit_output_ref(*task_key, output_ref.clone())?;

            let specifics = match task_key.kind() {
                TyKind::Bool
                | TyKind::Char
                | TyKind::Int(_)
                | TyKind::Uint(_)
                | TyKind::Float(_) => {
                    super::kinds::primitive::domain(*task_key, deps, &mut builder)?
                }
                TyKind::Closure(..) => {
                    super::kinds::closure::domain(*task_key, &output_ref, deps, &mut builder)?
                }
                TyKind::Adt(..) => {
                    super::kinds::adt::domain(*task_key, &output_ref, deps, &mut builder)?
                }
                TyKind::Tuple(..) => {
                    super::kinds::tuple::domain(*task_key, &output_ref, deps, &mut builder)?
                }
                TyKind::Never => super::kinds::never::domain(*task_key, deps, &mut builder)?,
                TyKind::Ref(_, _, ty::Mutability::Not) => {
                    super::kinds::immref::domain(*task_key, &output_ref, deps, &mut builder)?
                }
                TyKind::Ref(_, _, ty::Mutability::Mut) => {
                    super::kinds::mutref::domain(*task_key, deps, &mut builder)?
                }
                TyKind::Param(_) => super::kinds::param::domain(*task_key, deps, &mut builder)?,
                TyKind::Str => super::kinds::str::domain(*task_key, deps, &mut builder)?,
                _kind => super::kinds::opaque::domain(*task_key, deps, &mut builder)?,
            };
            Ok((builder.build(), specifics))
        })
    }
}

pub(crate) struct DomainBuilder<'vir> {
    pub(crate) vcx: &'vir vir::VirCtxt<'vir>,
    name: Option<&'vir str>,
    generics: Option<Vec<vir::LocalDeclTyVal<'vir>>>,
    domain_ident: Option<vir::DomainIdnCSnap<'vir>>,
    self_type: Option<vir::TypeCSnap<'vir>>,
    axioms: Vec<vir::DomainAxiom<'vir>>,
    functions: Vec<vir::DomainFunction<'vir>>,
}

impl<'vir> DomainBuilder<'vir> {
    pub(crate) fn new(vcx: &'vir vir::VirCtxt<'vir>) -> Self {
        DomainBuilder {
            vcx,
            name: None,
            generics: None,
            domain_ident: None,
            self_type: None,
            axioms: Vec::new(),
            functions: Vec::new(),
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
        self.functions
            .push(self.vcx.mk_domain_function(ident, false));
        ident
    }

    pub(crate) fn axiom(&mut self, name: &str, expr: vir::ExprBool<'vir>) {
        let name = vir::vir_format!(
            self.vcx,
            "{}_ax_{name}",
            self.name.expect("name should be set")
        );
        self.axioms
            .push(self.vcx.alloc(DomainAxiomData { name, expr }));
    }

    pub(crate) fn self_type(&self) -> vir::TypeCSnap<'vir> {
        self.self_type.expect("name should be set")
    }

    pub(crate) fn type_type(&self) -> vir::TypeTyVal<'vir> {
        vir::TYPE_TYVAL
    }

    pub(crate) fn output_ref(
        &self,
        base_name: String,
        typeof_function: FunctionIdn<'vir, vir::CSnap, vir::TyVal>,
        ty_param_accessors: &[FunctionIdn<'vir, vir::TyVal, vir::TyVal>],
    ) -> DomainEncOutputRef<'vir> {
        DomainEncOutputRef {
            base_name,
            domain: self.domain_ident.expect("name should be set").cast_ty(),
            typeof_function: typeof_function.cast_ty(typeof_function.arity().upcast_ty()),
            ty_param_accessors: self.vcx.alloc_slice(ty_param_accessors),
        }
    }

    pub(crate) fn build(self) -> Option<vir::Domain<'vir>> {
        Some(self.vcx.mk_domain(
            self.domain_ident?.name(),
            &[],
            self.vcx.alloc_slice(&self.axioms),
            self.vcx.alloc_slice(&self.functions),
        ))
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

    /// Information about the Rust type, only defined for fields that correspond
    /// to actual Rust types. For example, this will be `None` for a Viper
    /// `Bool` field encoded as part of the snapshot encoding of the rust bool
    /// type.
    pub(super) rust_ty_data: Option<LiftedRustTyData<'vir>>,
}

#[derive(Clone)]
pub(super) struct LiftedRustTyData<'vir> {
    /// The representation of the Rust type of the field
    lifted_ty: LiftedTy<'vir, ParamTy>,
    /// Takes as input the value of the field, and returns its type
    typeof_function: FunctionIdn<'vir, vir::Snap, vir::TyVal>,
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
            .map(|ty| Self::from_ty(vcx, deps, ty))
            .collect::<Result<Vec<_>, _>>()
    }

    pub(super) fn from_ty<T: TaskEncoder>(
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, T>,
        ty: ty::Ty<'vir>,
    ) -> Result<FieldTy<'vir>, EncodeFullError<'vir, T>> {
        let vir_ty = deps
            .require_ref::<RustTySnapshotsEnc>(ty)?
            .generic_snapshot
            .snapshot;
        let typeof_function = deps
            .require_ref::<DomainEnc>(extract_type_params(vcx.tcx(), ty).0)?
            .typeof_function;
        let lifted_ty = deps.require_local::<LiftedTyEnc<EncodeGenericsAsParamTy>>(ty)?;
        Ok(FieldTy {
            rust_ty: ty,
            ty: vir_ty,
            rust_ty_data: Some(LiftedRustTyData {
                lifted_ty,
                typeof_function,
            }),
        })
    }
}
