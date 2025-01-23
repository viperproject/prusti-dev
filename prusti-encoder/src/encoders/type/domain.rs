// TODO: this lint is something we should fix; to address there should probably
//   be an indirection in error storage somewhere, maybe even in `task-encoder`?
#![allow(clippy::result_large_err)]

use prusti_rustc_interface::{
    middle::ty::{self, util::IntTypeExt, IntTy, ParamTy, TyKind, UintTy},
    span::symbol,
    target::abi,
};
use task_encoder::{EncodeFullError, EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{
    BinaryArity, CallableIdent, DomainAxiomData, DomainFunctionData, DomainIdent, DomainParamData, FunctionIdent, NullaryArityAny, UnaryArity, UnknownArity
};

/// You probably never want to use this, use `SnapshotEnc` instead.
/// Note: there should never be a dependency on `PredicateEnc` inside this
/// encoder!
pub struct DomainEnc;

#[derive(Clone, Copy, Debug)]
pub struct FieldFunctions<'vir> {
    /// Snapshot of self as argument. Returns domain of field.
    pub read: FunctionIdent<'vir, UnaryArity<'vir>>,
    /// Snapshot of self as first argument and of field as second. Returns
    /// updated domain of self.
    pub write: FunctionIdent<'vir, BinaryArity<'vir>>,
}

#[derive(Clone, Copy, Debug)]
pub struct DomainDataPrim<'vir> {
    pub prim_type: vir::Type<'vir>,
    /// Snapshot of self as argument. Returns Viper primitive value.
    pub snap_to_prim: FunctionIdent<'vir, UnaryArity<'vir>>,
    /// Viper primitive value as argument. Returns domain.
    pub prim_to_snap: FunctionIdent<'vir, UnaryArity<'vir>>,
}
#[derive(Clone, Copy, Debug)]
pub struct DomainDataRef<'vir> {
    /// Construct domain from a `Ref` value.
    pub snap_to_prim: FunctionIdent<'vir, UnaryArity<'vir>>,
    /// Function to access the referee.
    pub deref_access: FunctionIdent<'vir, UnaryArity<'vir>>,
}
#[derive(Clone, Copy, Debug)]
pub struct DomainDataStruct<'vir> {
    /// Construct domain from snapshots of fields or for primitive types
    /// from the single Viper primitive value.
    pub field_snaps_to_snap: FunctionIdent<'vir, UnknownArity<'vir>>,
    /// Functions to access the fields.
    pub field_access: &'vir [FieldFunctions<'vir>],
}
#[derive(Clone, Copy, Debug)]
pub struct DomainDataEnum<'vir> {
    pub discr_ty: vir::Type<'vir>,
    pub discr_prim: DomainDataPrim<'vir>,
    //pub discr_bounds: DiscrBounds<'vir>,
    pub snap_to_discr_snap: FunctionIdent<'vir, UnaryArity<'vir>>,
    pub variants: &'vir [DomainDataVariant<'vir>],
}
#[derive(Clone, Copy, Debug)]
pub struct DomainDataVariant<'vir> {
    pub name: symbol::Symbol,
    pub vid: abi::VariantIdx,
    pub discr: vir::Expr<'vir>,
    pub fields: DomainDataStruct<'vir>,
}

#[derive(Clone, Copy, Debug)]
pub enum DiscrBounds<'vir> {
    Range {
        lower: vir::Expr<'vir>,
        upper: vir::Expr<'vir>,
    },
    Explicit(&'vir [vir::Expr<'vir>]),
}

#[derive(Clone, Copy, Debug)]
pub enum DomainEncSpecifics<'vir> {
    Param,
    Primitive(DomainDataPrim<'vir>),
    Ref(DomainDataRef<'vir>),
    // structs, tuples
    StructLike(DomainDataStruct<'vir>),
    EnumLike(Option<DomainDataEnum<'vir>>),
}

#[derive(Clone, Debug)]
pub struct DomainEncOutputRef<'vir> {
    pub base_name: String,
    pub domain: vir::DomainIdent<'vir, NullaryArityAny<'vir, DomainParamData<'vir>>>,
    pub(super) ty_param_accessors: &'vir [FunctionIdent<'vir, UnaryArity<'vir>>],
    /// Returns the Viper representation of the type of a snapshot-encoded value
    pub typeof_function: FunctionIdent<'vir, UnaryArity<'vir>>,
}

impl<'vir> DomainEncOutputRef<'vir> {
    /// Takes as input a snapshot encoding of a rust value, and returns
    /// the `idx`th type parameter of it's type.
    pub fn ty_param_from_snap(
        &self,
        vcx: &'vir vir::VirCtxt,
        idx: usize,
        snap: vir::Expr<'vir>,
    ) -> vir::Expr<'vir> {
        self.ty_param_accessors[idx].apply(vcx, [self.typeof_function.apply(vcx, [snap])])
    }
}

impl<'vir> task_encoder::OutputRefAny for DomainEncOutputRef<'vir> {}

use super::{
    lifted::ty::{EncodeGenericsAsParamTy, LiftedTy, LiftedTyEnc},
    most_generic_ty::{extract_type_params, MostGenericTy},
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
            let specifics = match task_key.kind() {
                TyKind::Bool
                | TyKind::Char
                | TyKind::Int(_)
                | TyKind::Uint(_)
                | TyKind::Float(_) => super::kinds::primitive::domain(*task_key, deps, &mut builder)?,
                TyKind::Closure(..) => super::kinds::closure::domain(*task_key, deps, &mut builder)?,
                TyKind::Adt(..) => super::kinds::adt::domain(*task_key, deps, &mut builder)?,
                TyKind::Tuple(..) => super::kinds::tuple::domain(*task_key, deps, &mut builder)?,
                TyKind::Never => super::kinds::never::domain(*task_key, deps, &mut builder)?,
                TyKind::Ref(..) => super::kinds::reference::domain(*task_key, deps, &mut builder)?,
                TyKind::Param(_) => super::kinds::param::domain(*task_key, deps, &mut builder)?,
                TyKind::Str => super::kinds::str::domain(*task_key, deps, &mut builder)?,
                kind => todo!("{kind:?}"),
            };
            Ok((builder.build(), specifics))
        })
    }
}

pub(crate) struct DomainBuilder<'vir> {
    pub(crate) vcx: &'vir vir::VirCtxt<'vir>,
    name: Option<&'vir str>,
    domain_ident: Option<vir::DomainIdent<'vir, NullaryArityAny<'vir, DomainParamData<'vir>>>>,
    self_type: Option<vir::Type<'vir>>,
    axioms: Vec<vir::DomainAxiom<'vir>>,
    functions: Vec<vir::DomainFunction<'vir>>,
}

impl<'vir> DomainBuilder<'vir> {
    pub(crate) fn new(
        vcx: &'vir vir::VirCtxt<'vir>,
    ) -> Self {
        DomainBuilder {
            vcx,
            name: None,
            domain_ident: None,
            self_type: None,
            axioms: Vec::new(),
            functions: Vec::new(),
        }
    }

    pub(crate) fn set_name(&mut self, name: &str) {
        let name = vir::vir_format!(self.vcx, "s_{name}");
        self.name = Some(name);
        self.domain_ident = Some(DomainIdent::nullary(vir::ViperIdent::new(name)));
        self.self_type = Some(self.vcx.alloc(vir::TypeData::Domain(self.name.expect("name should be set"), &[])));
    }

    pub(crate) fn function(
        &mut self,
        name: &str,
        args: &[&'vir vir::TypeData],
        ret: &'vir vir::TypeData,
    ) -> FunctionIdent<'vir, UnknownArity<'vir>> {
        let name = vir::vir_format!(self.vcx, "{}_{name}", self.name.expect("name should be set"));
        let args = self.vcx.alloc_slice(args);
        let ident = FunctionIdent::new(
            vir::ViperIdent::new(name),
            UnknownArity::new(args),
            ret,
        );
        self.functions.push(self.vcx.alloc(DomainFunctionData {
            unique: false,
            name: ident.name(),
            args,
            ret,
        }));
        ident
    }

    pub(crate) fn axiom(
        &mut self,
        name: &str,
        expr: vir::Expr<'vir>,
    ) {
        let name = vir::vir_format!(self.vcx, "{}_ax_{name}", self.name.expect("name should be set"));
        self.axioms.push(self.vcx.alloc(DomainAxiomData {
            name,
            expr,
        }));
    }

    pub(crate) fn self_type(&self) -> vir::Type<'vir> {
        self.self_type.expect("name should be set")
    }

    pub(crate) fn type_type(&self) -> vir::Type<'vir> {
        &vir::TypeData::Domain("Type", &[]) // TODO: refer to something else
    }

    pub(crate) fn output_ref(&self, base_name: String, typeof_function: FunctionIdent<'vir, UnaryArity<'vir>>) -> DomainEncOutputRef<'vir> {
        DomainEncOutputRef {
            base_name,
            domain: self.domain_ident.expect("name should be set"),
            typeof_function: typeof_function,
            ty_param_accessors: &[], /*self.vcx.alloc_slice(
                &self
                    .generics
                    .iter()
                    .map(|(_, ident)| *ident)
                    .collect::<Vec<_>>(),
            ),*/
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
    pub fn expect_ref(self) -> DomainDataRef<'vir> {
        match self {
            Self::Ref(data) => data,
            _ => panic!("expected ref"),
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
    pub fn expr_from_bits(&self, ty: ty::Ty<'vir>, value: u128) -> vir::Expr<'vir> {
        match *self.prim_type {
            vir::TypeData::Bool => {
                vir::with_vcx(|vcx| vcx.mk_const_expr(vir::ConstData::Bool(value != 0)))
            }
            vir::TypeData::Int => {
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
    /// The type of encoded field
    pub(super) ty: vir::Type<'vir>,

    /// Information about the Rust type, only defined for fields that correspond
    /// to actual Rust types. For example, this will be `None` for a Viper
    /// `Bool` field encoded as part of the snapshot encoding of the rust bool
    /// type.
    pub(super) rust_ty_data: Option<LiftedRustTyData<'vir>>,
}

#[derive(Clone)]
struct LiftedRustTyData<'vir> {
    /// The representation of the Rust type of the field
    lifted_ty: LiftedTy<'vir, ParamTy>,
    /// Takes as input the value of the field, and returns its type
    typeof_function: FunctionIdent<'vir, UnaryArity<'vir>>,
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
            ty: vir_ty,
            rust_ty_data: Some(LiftedRustTyData {
                lifted_ty,
                typeof_function,
            }),
        })
    }
}
