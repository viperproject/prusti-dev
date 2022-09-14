// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::{helpers::compute_discriminant_values, interface::MirTypeEncoderInterface};
use crate::encoder::{
    errors::{EncodingResult, ErrorCtxt, SpannedEncodingError, SpannedEncodingResult, WithSpan},
    mir::{
        constants::ConstantsEncoderInterface, errors::ErrorInterface,
        generics::MirGenericsEncoderInterface, pure::SpecificationEncoderInterface,
        specifications::SpecificationsInterface, types::helpers::compute_discriminant_ranges,
    },
    Encoder,
};
use log::debug;
use prusti_common::config;
use prusti_rustc_interface::{
    errors::MultiSpan,
    hir::def_id::DefId,
    middle::{
        mir,
        ty::{self, TypeVisitableExt},
    },
};
use vir_crate::high::{self as vir, operations::ty::Typed};

pub struct TypeEncoder<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p Encoder<'v, 'tcx>,
    ty: ty::Ty<'tcx>,
}

impl<'p, 'v, 'r: 'v, 'tcx: 'v> TypeEncoder<'p, 'v, 'tcx> {
    pub fn new(encoder: &'p Encoder<'v, 'tcx>, ty: ty::Ty<'tcx>) -> Self {
        TypeEncoder { encoder, ty }
    }

    fn encode_substs(
        &self,
        substs: prusti_rustc_interface::middle::ty::subst::SubstsRef<'tcx>,
    ) -> Vec<vir::Type> {
        encode_substs(self.encoder, substs)
    }

    fn is_mathematical_type(&self, did: DefId) -> bool {
        let type_name: &str = &self.encoder.env().name.get_absolute_item_name(did);
        matches!(
            type_name,
            "prusti_contracts::Seq"
                | "prusti_contracts::Map"
                | "prusti_contracts::Int"
                | "prusti_contracts::Ghost"
                | "prusti_contracts::Byte"
                | "prusti_contracts::Bytes"
        )
    }

    fn is_trusted_type(&self, adt_def: &ty::AdtDef) -> bool {
        if adt_def.is_struct() && !adt_def.is_box() && !adt_def.did().is_local() {
            let type_name: &str = &self
                .encoder
                .env()
                .name
                .get_absolute_item_name(adt_def.did());
            if !type_name.starts_with("prusti_contracts::") {
                return true;
            }
        }
        if let Some(type_specs) = self.encoder.get_type_specs(adt_def.did()) {
            *type_specs.trusted.expect_inherent()
        } else {
            false
        }
    }

    fn compute_array_len(&self, size: ty::Const<'tcx>) -> EncodingResult<u64> {
        self.encoder.compute_array_len(size)
    }

    #[tracing::instrument(level = "debug", skip(self), fields(ty = ?self.ty))]
    pub fn encode_type(self) -> SpannedEncodingResult<vir::Type> {
        // self.encode_polymorphic_predicate_use()
        let lifetimes = self.encoder.get_lifetimes_from_type_high(self.ty)?;
        let result = match self.ty.kind() {
            ty::TyKind::Bool => vir::Type::Bool,

            ty::TyKind::Int(ty::IntTy::I8) => vir::Type::Int(vir::ty::Int::I8),
            ty::TyKind::Int(ty::IntTy::I16) => vir::Type::Int(vir::ty::Int::I16),
            ty::TyKind::Int(ty::IntTy::I32) => vir::Type::Int(vir::ty::Int::I32),
            ty::TyKind::Int(ty::IntTy::I64) => vir::Type::Int(vir::ty::Int::I64),
            ty::TyKind::Int(ty::IntTy::I128) => vir::Type::Int(vir::ty::Int::I128),
            ty::TyKind::Int(ty::IntTy::Isize) => vir::Type::Int(vir::ty::Int::Isize),

            ty::TyKind::Uint(ty::UintTy::U8) => vir::Type::Int(vir::ty::Int::U8),
            ty::TyKind::Uint(ty::UintTy::U16) => vir::Type::Int(vir::ty::Int::U16),
            ty::TyKind::Uint(ty::UintTy::U32) => vir::Type::Int(vir::ty::Int::U32),
            ty::TyKind::Uint(ty::UintTy::U64) => vir::Type::Int(vir::ty::Int::U64),
            ty::TyKind::Uint(ty::UintTy::U128) => vir::Type::Int(vir::ty::Int::U128),
            ty::TyKind::Uint(ty::UintTy::Usize) => vir::Type::Int(vir::ty::Int::Usize),

            ty::TyKind::Char => vir::Type::Int(vir::ty::Int::Char),

            ty::TyKind::Float(ty::FloatTy::F32) => vir::Type::Float(vir::ty::Float::F32),
            ty::TyKind::Float(ty::FloatTy::F64) => vir::Type::Float(vir::ty::Float::F64),

            ty::TyKind::RawPtr(ty::TypeAndMut { ty, .. }) => {
                vir::Type::pointer(self.encoder.encode_type_high(*ty)?)
            }

            ty::TyKind::Ref(_region, ty, mutability) => {
                let lifetime = lifetimes.first().unwrap().clone();
                let uniqueness = self.encode_uniqueness(*mutability);
                vir::Type::reference(lifetime, uniqueness, self.encoder.encode_type_high(*ty)?)
            }

            ty::TyKind::Adt(adt_def, substs) if self.is_trusted_type(adt_def) => {
                vir::Type::trusted(
                    encode_trusted_name(self.encoder, adt_def.did()),
                    self.encode_substs(substs),
                    lifetimes,
                )
            }

            ty::TyKind::Adt(adt_def, substs) if adt_def.is_struct() => {
                let type_name: &str = &self
                    .encoder
                    .env()
                    .name
                    .get_absolute_item_name(adt_def.did());

                let enc_substs = self
                    .encode_substs(substs)
                    .into_iter()
                    .map(Box::new)
                    .collect::<Vec<_>>();

                // TODO: more stable reference to the Sequence type
                if type_name == "prusti_contracts::Seq" {
                    vir::Type::Sequence(vir::ty::Sequence {
                        element_type: enc_substs[0].clone(),
                        lifetimes,
                    })
                } else if type_name == "prusti_contracts::Map" {
                    vir::Type::Map(vir::ty::Map {
                        key_type: enc_substs[0].clone(),
                        val_type: enc_substs[1].clone(),
                        lifetimes,
                    })
                } else if type_name == "prusti_contracts::Int" {
                    vir::Type::Int(vir::ty::Int::Unbounded)
                } else if type_name == "prusti_contracts::Byte" {
                    vir::Type::MByte
                } else if type_name == "prusti_contracts::Bytes" {
                    vir::Type::MBytes
                } else if type_name == "prusti_contracts::Ghost" {
                    (*enc_substs[0]).clone()
                } else {
                    vir::Type::struct_(
                        encode_struct_name(self.encoder, adt_def.did()),
                        self.encode_substs(substs),
                        lifetimes,
                    )
                }
            }

            ty::TyKind::Adt(adt_def, substs) if adt_def.is_enum() => {
                if adt_def.variants().len() == 1 {
                    // FIXME: Currently fold-unfold assumes that everything that
                    // has only a single variant is a struct.
                    vir::Type::struct_(
                        encode_struct_name(self.encoder, adt_def.did()),
                        self.encode_substs(substs),
                        lifetimes,
                    )
                } else {
                    vir::Type::enum_(
                        encode_enum_name(self.encoder, adt_def.did()),
                        self.encode_substs(substs),
                        None,
                        lifetimes,
                    )
                }
            }

            ty::TyKind::Adt(adt_def, substs) if adt_def.is_union() => vir::Type::union_(
                encode_union_name(self.encoder, adt_def.did()),
                self.encode_substs(substs),
                None,
                lifetimes,
            ),

            ty::TyKind::Adt(_adt_def, _substs) => {
                unreachable!();
            }

            ty::TyKind::Tuple(elems) => vir::Type::tuple(
                elems
                    .iter()
                    .filter_map(|ty| self.encoder.encode_type_high(ty).ok())
                    .collect(),
                lifetimes,
            ),

            ty::TyKind::Never => vir::Type::Never,

            ty::TyKind::Str => vir::Type::Str,

            ty::TyKind::Array(elem_ty, size) => {
                // let (array_len, tail): (_, &[vir::Expression]) =
                //     if let Some((array_len, tail)) = const_arguments.split_first() {
                //         (array_len.clone(), tail)
                //     } else {
                //         let array_len: usize = self
                //             .compute_array_len(*size)
                //             .with_span(self.get_definition_span())?
                //             .try_into()
                //             .unwrap();
                //         (array_len.into(), &[])
                //     };
                let array_len: usize = self
                    .compute_array_len(*size)
                    .with_span(self.get_definition_span())?
                    .try_into()
                    .unwrap();
                let lifetimes = self.encoder.get_lifetimes_from_type_high(*elem_ty)?;
                vir::Type::array(
                    vir::ty::ConstGenericArgument::new(Some(Box::new(array_len.into()))),
                    self.encoder.encode_type_high(*elem_ty)?,
                    lifetimes,
                )
            }

            ty::TyKind::Slice(elem_ty) => {
                vir::Type::slice(self.encoder.encode_type_high(*elem_ty)?, lifetimes)
            }

            ty::TyKind::Closure(def_id, _substs) => vir::Type::closure(
                encode_closure_name(self.encoder, *def_id),
                // FIXME: We are currently ignoring type arguments and lifetimes.
                // self.encode_substs(substs),
                // lifetimes,
            ),

            ty::TyKind::FnDef(def_id, _substs) => vir::Type::function_def(
                encode_function_def_name(self.encoder, *def_id),
                // FIXME: We are currently ignoring type arguments and lifetimes.
                // self.encode_substs(substs),
                // lifetimes,
            ),

            ty::TyKind::Param(param_ty) => {
                vir::Type::TypeVar(self.encoder.encode_param(param_ty.name, param_ty.index))
            }

            ty::TyKind::Alias(ty::AliasKind::Projection, ty::AliasTy { def_id, substs, .. }) => {
                vir::Type::projection(
                    self.encoder.encode_item_name(*def_id),
                    self.encode_substs(substs),
                    lifetimes,
                )
            }

            ty::TyKind::Dynamic(..) => vir::Type::unsupported("dynamic".to_string()),

            ty::TyKind::FnPtr(..) => vir::Type::unsupported("fnptr".to_string()),

            ty::TyKind::Foreign(..) => vir::Type::unsupported("foreign".to_string()),

            ty => vir::Type::unsupported(crate::utils::ty_to_string(ty)),
        };
        Ok(result)
    }

    pub fn get_definition_span(&self) -> MultiSpan {
        match self.ty.kind() {
            ty::TyKind::Bool
            | ty::TyKind::Char
            | ty::TyKind::Int(_)
            | ty::TyKind::Uint(_)
            | ty::TyKind::Float(_)
            | ty::TyKind::Str
            | ty::TyKind::Array(_, _)
            | ty::TyKind::Slice(_)
            | ty::TyKind::RawPtr(_)
            | ty::TyKind::Ref(_, _, _)
            | ty::TyKind::FnPtr(_)
            | ty::TyKind::Dynamic(..)
            | ty::TyKind::GeneratorWitness(..)
            | ty::TyKind::GeneratorWitnessMIR(..)
            | ty::TyKind::Never
            | ty::TyKind::Tuple(_)
            | ty::TyKind::Alias(ty::AliasKind::Projection, _)
            | ty::TyKind::Param(_)
            | ty::TyKind::Bound(..)
            | ty::TyKind::Placeholder(_)
            | ty::TyKind::Infer(_)
            | ty::TyKind::Error(_) => MultiSpan::new(),
            ty::TyKind::Adt(adt, _) => self.encoder.env().query.get_def_span(adt.did()).into(),
            ty::TyKind::Foreign(did)
            | ty::TyKind::FnDef(did, _)
            | ty::TyKind::Closure(did, _)
            | ty::TyKind::Generator(did, _, _)
            | ty::TyKind::Alias(ty::AliasKind::Opaque, ty::AliasTy { def_id: did, .. }) => {
                self.encoder.env().query.get_def_span(did).into()
            }
        }
    }

    pub fn get_integer_bounds(&self) -> Option<(vir::Expression, vir::Expression)> {
        match self.ty.kind() {
            ty::TyKind::Int(int_ty) => {
                let (mut low, mut up): (vir::Expression, vir::Expression) = match int_ty {
                    ty::IntTy::I8 => (std::i8::MIN.into(), std::i8::MAX.into()),
                    ty::IntTy::I16 => (std::i16::MIN.into(), std::i16::MAX.into()),
                    ty::IntTy::I32 => (std::i32::MIN.into(), std::i32::MAX.into()),
                    ty::IntTy::I64 => (std::i64::MIN.into(), std::i64::MAX.into()),
                    ty::IntTy::I128 => (std::i128::MIN.into(), std::i128::MAX.into()),
                    ty::IntTy::Isize => (std::isize::MIN.into(), std::isize::MAX.into()),
                };
                low.set_type(vir::Type::MInt);
                up.set_type(vir::Type::MInt);
                Some((low, up))
            }
            ty::TyKind::Uint(uint_ty) => {
                let (mut low, mut up): (vir::Expression, vir::Expression) = match uint_ty {
                    ty::UintTy::U8 => (0.into(), std::u8::MAX.into()),
                    ty::UintTy::U16 => (0.into(), std::u16::MAX.into()),
                    ty::UintTy::U32 => (0.into(), std::u32::MAX.into()),
                    ty::UintTy::U64 => (0.into(), std::u64::MAX.into()),
                    ty::UintTy::U128 => (0.into(), std::u128::MAX.into()),
                    ty::UintTy::Usize => (0.into(), std::usize::MAX.into()),
                };
                low.set_type(vir::Type::MInt);
                up.set_type(vir::Type::MInt);
                Some((low, up))
            }
            ty::TyKind::Char => {
                let mut low: vir::Expression = 0.into();
                let mut up: vir::Expression = std::char::MAX.into();
                low.set_type(vir::Type::MInt);
                up.set_type(vir::Type::MInt);
                Some((low, up))
            }
            ty::TyKind::Ref(_, ty, _) => Self::new(self.encoder, *ty).get_integer_bounds(),
            _ => None,
        }
    }

    pub fn get_float_bounds(&self) -> Option<(vir::Expression, vir::Expression)> {
        match self.ty.kind() {
            ty::TyKind::Float(float_ty) => {
                let bounds = match float_ty {
                    ty::FloatTy::F32 => (std::f32::MIN.into(), std::f32::MAX.into()),
                    ty::FloatTy::F64 => (std::f64::MIN.into(), std::f64::MAX.into()),
                };
                Some(bounds)
            }
            _ => None,
        }
    }

    /// Encodes a type predicate for the given type.
    #[tracing::instrument(level = "debug", skip(self), fields(ty = ?self.ty))]
    pub fn encode_type_def_high(
        self,
        ty: &vir::Type,
        with_invariant: bool,
    ) -> SpannedEncodingResult<vir::TypeDecl> {
        let type_decl = match self.ty.kind() {
            ty::TyKind::Bool => vir::TypeDecl::bool(),
            ty::TyKind::Int(_) | ty::TyKind::Uint(_) | ty::TyKind::Char => {
                let mut lower_bound = None;
                let mut upper_bound = None;
                if config::check_overflows() {
                    if let Some((lower, upper)) = self.get_integer_bounds() {
                        lower_bound = Some(Box::new(lower));
                        upper_bound = Some(Box::new(upper));
                    }
                }
                if config::encode_unsigned_num_constraint() && lower_bound.is_none() {
                    if let ty::TyKind::Uint(_) = self.ty.kind() {
                        let mut bound: vir::Expression = 0usize.into();
                        bound.set_type(vir::Type::MInt);
                        lower_bound = Some(Box::new(bound));
                    }
                }
                vir::TypeDecl::int(lower_bound, upper_bound)
            }
            ty::TyKind::Float(_) => {
                let mut lower_bound = None;
                let mut upper_bound = None;
                if config::check_overflows() {
                    if let Some((lower, upper)) = self.get_float_bounds() {
                        lower_bound = Some(Box::new(lower));
                        upper_bound = Some(Box::new(upper));
                    }
                }
                vir::TypeDecl::float(lower_bound, upper_bound)
            }
            ty::TyKind::RawPtr(prusti_rustc_interface::middle::ty::TypeAndMut { ty, mutbl: _ }) => {
                // FIXME: Remove code duplication with ty::TyKind::Array
                let const_parameters = self.encoder.get_const_parameters_from_type_high(self.ty)?;
                let const_arguments: Vec<_> = const_parameters
                    .iter()
                    .cloned()
                    .map(|argument| argument.into())
                    .collect();
                let target_type = self
                    .encoder
                    .encode_type_high(*ty)?
                    .replace_const_arguments_with(const_arguments);
                let lifetimes = self.encoder.get_lifetimes_from_type_high(self.ty)?;
                vir::TypeDecl::pointer(lifetimes, const_parameters, target_type)
            }
            ty::TyKind::Ref(_, ty, mutability) => {
                // FIXME: Remove code duplication with ty::TyKind::Array
                let const_parameters = self.encoder.get_const_parameters_from_type_high(self.ty)?;
                let const_arguments: Vec<_> = const_parameters
                    .iter()
                    .cloned()
                    .map(|argument| argument.into())
                    .collect();
                let target_type = self
                    .encoder
                    .encode_type_high(*ty)?
                    .replace_const_arguments_with(const_arguments);
                let lifetimes = self.encoder.get_lifetimes_from_type_high(self.ty)?;
                vir::TypeDecl::reference(
                    lifetimes,
                    const_parameters,
                    self.encode_uniqueness(*mutability),
                    target_type,
                )
            }
            ty::TyKind::Tuple(elems) => {
                let lifetimes = self.encoder.get_lifetimes_from_substs(elems.as_substs())?;
                let const_parameters = self
                    .encoder
                    .get_const_parameters_from_substs(elems.as_substs())?;
                let arguments = elems
                    .into_iter()
                    .map(|ty| self.encoder.encode_type_high(ty))
                    .collect::<Result<_, _>>()?;
                vir::TypeDecl::tuple(lifetimes, const_parameters, arguments)
            }
            ty::TyKind::Adt(adt_def, substs) if self.is_mathematical_type(adt_def.did()) => {
                let lifetimes = self.encoder.get_lifetimes_from_substs(substs)?;
                let const_parameters = self.encoder.get_const_parameters_from_substs(substs)?;
                let type_name: &str = &self
                    .encoder
                    .env()
                    .name
                    .get_absolute_item_name(adt_def.did());
                let enc_substs = self.encode_substs(substs).into_iter().collect::<Vec<_>>();
                match type_name {
                    "prusti_contracts::Seq" => {
                        vir::TypeDecl::sequence(lifetimes, const_parameters, enc_substs[0].clone())
                    }
                    "prusti_contracts::Map" => vir::TypeDecl::map(
                        lifetimes,
                        const_parameters,
                        enc_substs[0].clone(),
                        enc_substs[1].clone(),
                    ),
                    "prusti_contracts::Int" => vir::TypeDecl::Int(vir::type_decl::Int {
                        lower_bound: None,
                        upper_bound: None,
                    }),
                    "prusti_contracts::Ghost" => {
                        if let ty::subst::GenericArgKind::Type(ty) = substs[0].unpack() {
                            let encoded_type = Self::new(self.encoder, ty).encode_type()?;
                            Self::new(self.encoder, ty)
                                .encode_type_def_high(&encoded_type, with_invariant)?
                        } else {
                            unreachable!("no type parameter given for Ghost<T>")
                        }
                    }
                    "prusti_contracts::Bytes" | "prusti_contracts::Byte" => vir::TypeDecl::trusted(
                        encode_trusted_name(self.encoder, adt_def.did()),
                        Vec::new(),
                        Vec::new(),
                    ),
                    _ => {
                        unreachable!("unexpected mathematical type: {type_name}");
                    }
                }
            }
            ty::TyKind::Adt(adt_def, substs) if self.is_trusted_type(adt_def) => {
                let lifetimes = self.encoder.get_lifetimes_from_substs(substs)?;
                let const_parameters = self.encoder.get_const_parameters_from_substs(substs)?;
                vir::TypeDecl::trusted(
                    encode_trusted_name(self.encoder, adt_def.did()),
                    lifetimes,
                    const_parameters,
                )
            }
            ty::TyKind::Adt(adt_def, substs) => encode_adt_def(
                self.encoder,
                ty,
                self.ty,
                *adt_def,
                substs,
                None,
                with_invariant,
            )?,
            ty::TyKind::Never => vir::TypeDecl::never(),
            ty::TyKind::Param(param_ty) => {
                vir::TypeDecl::type_var(param_ty.name.as_str().to_string())
            }
            ty::TyKind::Closure(def_id, internal_substs) => {
                let cl_substs = internal_substs.as_closure();
                let arguments = cl_substs
                    .upvar_tys()
                    .filter_map(|ty| self.encoder.encode_type_high(ty).ok())
                    .collect();
                let name = encode_closure_name(self.encoder, *def_id);
                vir::TypeDecl::closure(name, arguments)
            }
            ty::TyKind::Array(elem_ty, _size) => {
                let lifetimes = self.encoder.get_lifetimes_from_type_high(self.ty)?;
                let const_parameters = self.encoder.get_const_parameters_from_type_high(self.ty)?;
                let const_arguments: Vec<_> = const_parameters
                    .iter()
                    .skip(1)
                    .cloned()
                    .map(|argument| argument.into())
                    .collect();
                let element_type = self
                    .encoder
                    .encode_type_high(*elem_ty)?
                    .replace_const_arguments_with(const_arguments);
                vir::TypeDecl::array(lifetimes, const_parameters, element_type)
            }
            ty::TyKind::Slice(elem_ty) => {
                let lifetimes = self.encoder.get_lifetimes_from_type_high(self.ty)?;
                let const_parameters = self.encoder.get_const_parameters_from_type_high(self.ty)?;
                let const_arguments: Vec<_> = const_parameters
                    .iter()
                    .cloned()
                    .map(|argument| argument.into())
                    .collect();
                let element_type = self
                    .encoder
                    .encode_type_high(*elem_ty)?
                    .replace_const_arguments_with(const_arguments);
                vir::TypeDecl::slice(lifetimes, const_parameters, element_type)
            }
            ref ty_variant => {
                debug!("Encoding of type '{:?}' is incomplete", ty_variant);
                let ty = self.encoder.encode_type_high(self.ty)?;
                vir::TypeDecl::unsupported(ty)
            }
        };
        Ok(type_decl)
    }

    // fn encode_polymorphic_predicate_use(self) -> EncodingResult<vir::Type> {
    //     debug!("Encode type predicate name '{:?}'", self.ty);

    //     let result = match self.ty.kind() {
    //         ty::TyKind::Bool => vir::Type::typed_ref("bool"),

    //         ty::TyKind::Int(ty::IntTy::I8) => vir::Type::typed_ref("i8"),
    //         ty::TyKind::Int(ty::IntTy::I16) => vir::Type::typed_ref("i16"),
    //         ty::TyKind::Int(ty::IntTy::I32) => vir::Type::typed_ref("i32"),
    //         ty::TyKind::Int(ty::IntTy::I64) => vir::Type::typed_ref("i64"),
    //         ty::TyKind::Int(ty::IntTy::I128) => vir::Type::typed_ref("i128"),
    //         ty::TyKind::Int(ty::IntTy::Isize) => vir::Type::typed_ref("isize"),

    //         ty::TyKind::Uint(ty::UintTy::U8) => vir::Type::typed_ref("u8"),
    //         ty::TyKind::Uint(ty::UintTy::U16) => vir::Type::typed_ref("u16"),
    //         ty::TyKind::Uint(ty::UintTy::U32) => vir::Type::typed_ref("u32"),
    //         ty::TyKind::Uint(ty::UintTy::U64) => vir::Type::typed_ref("u64"),
    //         ty::TyKind::Uint(ty::UintTy::U128) => vir::Type::typed_ref("u128"),
    //         ty::TyKind::Uint(ty::UintTy::Usize) => vir::Type::typed_ref("usize"),

    //         ty::TyKind::Char => vir::Type::typed_ref("char"),

    //         ty::TyKind::RawPtr(ty::TypeAndMut { ty, .. }) => {
    //             vir::Type::typed_ref_with_args("raw_ref", vec![self.encoder.encode_type(ty)?])
    //         }
    //         ty::TyKind::Ref(_, ty, _) => {
    //             vir::Type::typed_ref_with_args("ref", vec![self.encoder.encode_type(ty)?])
    //         }

    //         ty::TyKind::Adt(adt_def, subst) => vir::Type::typed_ref_with_args(
    //             format!("adt${}", self.encoder.encode_item_name(adt_def.did)),
    //             subst
    //                 .iter()
    //                 .filter_map(|kind| {
    //                     if let ty::subst::GenericArgKind::Type(ty) = kind.unpack() {
    //                         self.encoder.encode_type(ty).ok()
    //                     } else {
    //                         None
    //                     }
    //                 })
    //                 .collect(),
    //         ),

    //         ty::TyKind::Tuple(elems) => vir::Type::typed_ref_with_args(
    //             "tuple",
    //             elems
    //                 .iter()
    //                 .filter_map(|ty| self.encoder.encode_type(ty).ok())
    //                 .collect(),
    //         ),

    //         ty::TyKind::Never => vir::Type::typed_ref("never"),

    //         ty::TyKind::Str => vir::Type::typed_ref("str"),

    //         ty::TyKind::Array(elem_ty, size) => {
    //             let array_len = self
    //                 .encoder
    //                 .const_eval_intlike(&size.kind)
    //                 .unwrap()
    //                 .to_u64()
    //                 .unwrap();
    //             vir::Type::typed_ref_with_args(
    //                 format!("Array${}", array_len),
    //                 vec![self.encoder.encode_type(elem_ty)?],
    //             )
    //         }

    //         ty::TyKind::Slice(elem_ty) => {
    //             vir::Type::typed_ref_with_args("Slice", vec![self.encoder.encode_type(elem_ty)?])
    //         }

    //         ty::TyKind::Closure(def_id, closure_subst) => vir::Type::typed_ref_with_args(
    //             format!(
    //                 "closure${}_{}",
    //                 def_id.krate.as_u32(),
    //                 def_id.index.as_u32()
    //             ),
    //             closure_subst
    //                 .iter()
    //                 .filter_map(|kind| {
    //                     if let ty::subst::GenericArgKind::Type(ty) = kind.unpack() {
    //                         self.encoder.encode_type(ty).ok()
    //                     } else {
    //                         None
    //                     }
    //                 })
    //                 .collect(),
    //         ),

    //         ty::TyKind::Param(param_ty) => {
    //             vir::Type::type_var(format!("{}", param_ty.name.as_str()))
    //         }

    //         ty::TyKind::Projection(ty::ProjectionTy {
    //             item_def_id,
    //             substs,
    //         }) => vir::Type::typed_ref_with_args(
    //             self.encoder.encode_item_name(*item_def_id),
    //             substs
    //                 .iter()
    //                 .filter_map(|kind| {
    //                     if let ty::subst::GenericArgKind::Type(ty) = kind.unpack() {
    //                         self.encoder.encode_type(ty).ok()
    //                     } else {
    //                         None
    //                     }
    //                 })
    //                 .collect(),
    //         ),

    //         ty::TyKind::Dynamic(..) => vir::Type::typed_ref("unsupported$dynamic"),

    //         ty::TyKind::FnPtr(..) => vir::Type::typed_ref("unsupported$fnptr"),

    //         ty::TyKind::FnDef(..) => vir::Type::typed_ref("unsupported$fndef"),

    //         ty::TyKind::Foreign(..) => vir::Type::typed_ref("unsupported$foreign"),

    //         _ => vir::Type::typed_ref("unsupported"),
    //     };
    //     Ok(result)
    // }

    fn encode_uniqueness(&self, mutability: mir::Mutability) -> vir::ty::Uniqueness {
        match mutability {
            mir::Mutability::Mut => vir::ty::Uniqueness::Unique,
            mir::Mutability::Not => vir::ty::Uniqueness::Shared,
        }
    }
}

fn encode_substs<'v, 'tcx: 'v>(
    encoder: &Encoder<'v, 'tcx>,
    substs: prusti_rustc_interface::middle::ty::subst::SubstsRef<'tcx>,
) -> Vec<vir::Type> {
    substs
        .iter()
        .filter_map(|kind| {
            if let ty::subst::GenericArgKind::Type(ty) = kind.unpack() {
                encoder.encode_type_high(ty).ok()
            } else {
                None
            }
        })
        .collect()
}

fn encode_enum_name<'v, 'tcx: 'v>(encoder: &Encoder<'v, 'tcx>, did: DefId) -> String {
    format!("enum${}", encoder.encode_item_name(did))
}

fn encode_union_name<'v, 'tcx: 'v>(encoder: &Encoder<'v, 'tcx>, did: DefId) -> String {
    format!("union${}", encoder.encode_item_name(did))
}

fn encode_closure_name<'v, 'tcx: 'v>(encoder: &Encoder<'v, 'tcx>, did: DefId) -> String {
    format!("closure${}", encoder.encode_item_name(did))
}

fn encode_function_def_name<'v, 'tcx: 'v>(encoder: &Encoder<'v, 'tcx>, did: DefId) -> String {
    format!("fndef${}", encoder.encode_item_name(did))
}

fn encode_box_name() -> String {
    "box$".to_string()
}

fn encode_struct_name<'v, 'tcx: 'v>(encoder: &Encoder<'v, 'tcx>, did: DefId) -> String {
    format!("struct${}", encoder.encode_item_name(did))
}

fn encode_trusted_name<'v, 'tcx: 'v>(encoder: &Encoder<'v, 'tcx>, did: DefId) -> String {
    format!("trusted${}", encoder.encode_item_name(did))
}

fn encode_variant<'v, 'tcx: 'v>(
    encoder: &Encoder<'v, 'tcx>,
    name: String,
    mir_type: ty::Ty<'tcx>,
    substs: ty::subst::SubstsRef<'tcx>,
    variant: &ty::VariantDef,
    mut structural_invariant: Option<Vec<vir::Expression>>,
    def_id: Option<DefId>,
) -> SpannedEncodingResult<vir::type_decl::Struct> {
    let tcx = encoder.env().tcx();
    if structural_invariant.is_some() {
        let def_id = def_id.unwrap();
        // Get the module containing the given `def_id`.
        let module = tcx
            .parent_module_from_def_id(def_id.as_local().unwrap())
            .to_def_id();
        // Check that all fields are private.
        for field in &variant.fields {
            match field.vis {
                ty::Visibility::Restricted(field_visibility_module)
                    if field_visibility_module == module =>
                {
                    // The field is private.
                }
                _ => {
                    unimplemented!(
                        "TODO: A proper error message that the field {field:?} must be private"
                    );
                }
            }
        }
    }
    let mut fields = Vec::new();
    for (field_index, field) in variant.fields.iter().enumerate() {
        let field_name = crate::encoder::encoder::encode_field_name(field.ident(tcx).as_str());
        let field_ty = field.ty(tcx, substs);
        let field_ty = if config::unsafe_core_proof() && field_ty.has_erasable_regions() {
            field_ty
        } else {
            tcx.try_normalize_erasing_regions(ty::ParamEnv::reveal_all(), field_ty)
                .unwrap_or(field_ty)
        };
        let field =
            vir::FieldDecl::new(field_name, field_index, encoder.encode_type_high(field_ty)?);
        fields.push(field);
    }
    let lifetimes = encoder.get_lifetimes_from_substs(substs)?;
    let const_parameters = encoder.get_const_parameters_from_substs(substs)?;
    let position = if let Some(def_id) = def_id {
        let span = encoder.env().query.get_def_span(def_id);
        let position = encoder
            .error_manager()
            .register_error(span, ErrorCtxt::TypeInvariantDefinition, def_id)
            .into();
        if let Some(structural_invariant) = &mut structural_invariant {
            for expression in std::mem::take(structural_invariant) {
                structural_invariant.push(encoder.set_surrounding_error_context_for_expression(
                    expression,
                    position,
                    ErrorCtxt::TypeInvariantDefinition,
                ));
            }
        }
        position
    } else {
        Default::default()
    };
    let size = if let Ok(layout) = tcx.layout_of(ty::ParamEnv::reveal_all().and(mir_type)) {
        Some(layout.size.bytes())
    } else {
        None
    };
    let variant = vir::type_decl::Struct::new_with_pos(
        name,
        lifetimes,
        const_parameters,
        structural_invariant,
        fields,
        size,
        position,
    );
    Ok(variant)
}

fn encode_structural_invariant<'v, 'tcx: 'v>(
    encoder: &Encoder<'v, 'tcx>,
    ty: &vir::Type,
    substs: ty::subst::SubstsRef<'tcx>,
    did: DefId,
) -> SpannedEncodingResult<Option<Vec<vir::Expression>>> {
    let invariant = if let Some(specs) = encoder.get_type_specs(did) {
        match &specs.structural_invariant {
            prusti_interface::specs::typed::SpecificationItem::Empty => None,
            prusti_interface::specs::typed::SpecificationItem::Inherent(invs) => {
                Some(
                    invs.iter()
                        .map(|inherent_def_id| {
                            encoder.encode_assertion_high(
                                *inherent_def_id,
                                None,
                                &[vir::Expression::self_variable(ty.clone())],
                                None,
                                // true,
                                *inherent_def_id,
                                substs,
                            )
                        })
                        .collect::<Result<Vec<_>, _>>()?,
                )
            }
            _ => todo!(),
            // TODO(inv): handle invariant inheritance
        }
    } else {
        None
    };
    Ok(invariant)
}

/// `with_invariant` is used to break infinite recursion.
#[tracing::instrument(level = "debug", skip(encoder))]
pub(super) fn encode_adt_def<'v, 'tcx>(
    encoder: &Encoder<'v, 'tcx>,
    ty: &vir::Type,
    mir_type: ty::Ty<'tcx>,
    adt_def: ty::AdtDef<'tcx>,
    substs: ty::subst::SubstsRef<'tcx>,
    variant_index: Option<prusti_rustc_interface::target::abi::VariantIdx>,
    with_invariant: bool,
) -> SpannedEncodingResult<vir::TypeDecl> {
    let lifetimes = encoder.get_lifetimes_from_substs(substs)?;
    let const_parameters = encoder.get_const_parameters_from_substs(substs)?;
    let structural_invariant = if with_invariant {
        encode_structural_invariant(encoder, ty, substs, adt_def.did())?
    } else {
        None
    };
    let tcx = encoder.env().tcx();
    if adt_def.is_box() {
        debug!("ADT {:?} is a box", adt_def);
        assert!(variant_index.is_none());
        let boxed_ty = encoder.encode_type_high(substs.type_at(0))?;
        let field = vir::FieldDecl::new("val_ref", 0usize, boxed_ty);
        Ok(vir::TypeDecl::struct_(
            encode_box_name(),
            lifetimes,
            const_parameters,
            structural_invariant,
            vec![field],
            None,
            Default::default(),
        ))
    } else if adt_def.is_struct() {
        debug!("ADT {:?} is a struct", adt_def);
        assert!(variant_index.is_none());
        let name = encode_struct_name(encoder, adt_def.did());
        let variant = adt_def.non_enum_variant();
        Ok(vir::TypeDecl::Struct(encode_variant(
            encoder,
            name,
            mir_type,
            substs,
            variant,
            structural_invariant,
            Some(adt_def.did()),
        )?))
    } else if adt_def.is_union() {
        debug!("ADT {:?} is a union", adt_def);
        if structural_invariant.is_some() {
            return Err(SpannedEncodingError::unsupported(
                "Structural invariants are not supported on unions",
                encoder.env().query.get_def_span(adt_def.did()),
            ));
        }
        if !config::unsafe_core_proof() {
            return Err(SpannedEncodingError::unsupported(
                "unions are not supported",
                encoder.env().query.get_def_span(adt_def.did()),
            ));
        }
        assert!(variant_index.is_none());
        let name = encode_union_name(encoder, adt_def.did());
        // We treat union fields as variants.
        let variant = adt_def.non_enum_variant();
        let num_variants: i128 = variant.fields.len().try_into().unwrap();
        let discriminant_bounds = (0, num_variants - 1);
        let discriminant_values = (0..num_variants).collect();
        let mut variants = Vec::new();
        for (field_index, field) in variant.fields.iter().enumerate() {
            let field_name = field.ident(tcx).as_str().to_string();
            let field_ty = field.ty(tcx, substs);
            let encoded_field =
                vir::FieldDecl::new("value", field_index, encoder.encode_type_high(field_ty)?);
            let variant = vir::type_decl::Struct::new(
                field_name,
                lifetimes.clone(),
                const_parameters.clone(),
                None,
                vec![encoded_field],
                None,
            );
            variants.push(variant);
        }
        Ok(vir::TypeDecl::union_(
            name,
            encode_substs(encoder, substs),
            vir::Type::Int(vir::ty::Int::Usize),
            vec![discriminant_bounds],
            discriminant_values,
            variants,
            lifetimes,
            const_parameters,
        ))
    } else if adt_def.is_enum() {
        debug!("ADT {:?} is an enum", adt_def);
        if structural_invariant.is_some() {
            return Err(SpannedEncodingError::unsupported(
                "Structural invariants are not supported on enums",
                encoder.env().query.get_def_span(adt_def.did()),
            ));
        }
        let name = encode_enum_name(encoder, adt_def.did());
        let num_variants = adt_def.variants().len();
        debug!("ADT {:?} is enum with {} variants", adt_def, num_variants);
        let type_decl = if num_variants == 1 {
            // FIXME: Currently fold-unfold assumes that everything that
            // has only a single variant is a struct.
            let variant = &adt_def.variants()[0usize.into()];
            vir::TypeDecl::Struct(encode_variant(
                encoder,
                name,
                mir_type,
                substs,
                variant,
                None,
                Default::default(),
            )?)
        } else if let Some(_variant_index) = variant_index {
            // let variant = &adt_def.variants()[variant_index];
            // vir::TypeDecl::Struct(encode_variant(encoder, name, substs, variant)?)
            unimplemented!("FIXME: How this should be implemented?")
        } else {
            let discriminant_bounds = compute_discriminant_ranges(adt_def, tcx);
            let discriminant_values = compute_discriminant_values(adt_def, tcx)
                .into_iter()
                .collect();
            let mut variants = Vec::new();
            for variant in adt_def.variants() {
                let name = variant.ident(tcx).to_string();
                let encoded_variant = encode_variant(
                    encoder,
                    name,
                    mir_type,
                    substs,
                    variant,
                    None,
                    Default::default(),
                )?;
                variants.push(encoded_variant);
            }
            let mir_discriminant_type = match adt_def.repr().discr_type() {
                prusti_rustc_interface::target::abi::IntegerType::Fixed(int, signed) => {
                    if signed {
                        let int = match int {
                            prusti_rustc_interface::target::abi::Integer::I8 => {
                                prusti_rustc_interface::middle::ty::IntTy::I8
                            }
                            prusti_rustc_interface::target::abi::Integer::I16 => {
                                prusti_rustc_interface::middle::ty::IntTy::I16
                            }
                            prusti_rustc_interface::target::abi::Integer::I32 => {
                                prusti_rustc_interface::middle::ty::IntTy::I32
                            }
                            prusti_rustc_interface::target::abi::Integer::I64 => {
                                prusti_rustc_interface::middle::ty::IntTy::I64
                            }
                            prusti_rustc_interface::target::abi::Integer::I128 => {
                                prusti_rustc_interface::middle::ty::IntTy::I128
                            }
                        };
                        encoder.env().tcx().mk_ty_from_kind(ty::TyKind::Int(int))
                    } else {
                        let int = match int {
                            prusti_rustc_interface::target::abi::Integer::I8 => {
                                prusti_rustc_interface::middle::ty::UintTy::U8
                            }
                            prusti_rustc_interface::target::abi::Integer::I16 => {
                                prusti_rustc_interface::middle::ty::UintTy::U16
                            }
                            prusti_rustc_interface::target::abi::Integer::I32 => {
                                prusti_rustc_interface::middle::ty::UintTy::U32
                            }
                            prusti_rustc_interface::target::abi::Integer::I64 => {
                                prusti_rustc_interface::middle::ty::UintTy::U64
                            }
                            prusti_rustc_interface::target::abi::Integer::I128 => {
                                prusti_rustc_interface::middle::ty::UintTy::U128
                            }
                        };
                        encoder.env().tcx().mk_ty_from_kind(ty::TyKind::Uint(int))
                    }
                }
                prusti_rustc_interface::target::abi::IntegerType::Pointer(signed) => {
                    if signed {
                        encoder.env().tcx().mk_ty_from_kind(ty::TyKind::Int(
                            prusti_rustc_interface::middle::ty::IntTy::Isize,
                        ))
                    } else {
                        encoder.env().tcx().mk_ty_from_kind(ty::TyKind::Uint(
                            prusti_rustc_interface::middle::ty::UintTy::Usize,
                        ))
                    }
                }
            };
            let discriminant_type = encoder.encode_type_high(mir_discriminant_type)?;
            vir::TypeDecl::enum_(
                name,
                encode_substs(encoder, substs),
                discriminant_type,
                discriminant_bounds,
                discriminant_values,
                variants,
                lifetimes,
                const_parameters,
            )
        };
        Ok(type_decl)
    } else {
        Err(SpannedEncodingError::internal(
            format!("unexpected variant of adt_def: {adt_def:?}"),
            encoder.env().query.get_def_span(adt_def.did()),
        ))
    }
}
