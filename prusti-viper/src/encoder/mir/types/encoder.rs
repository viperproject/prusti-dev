// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::{helpers::compute_discriminant_values, interface::MirTypeEncoderInterface};
use crate::encoder::{
    errors::{EncodingResult, SpannedEncodingError, SpannedEncodingResult},
    high::types::HighTypeEncoderInterface,
    mir::{generics::MirGenericsEncoderInterface, types::helpers::compute_discriminant_ranges},
    Encoder,
};
use log::debug;
use prusti_common::config;
use prusti_interface::environment::mir_dump::graphviz::ToText;
use rustc_hir::def_id::DefId;
use rustc_middle::{mir, ty};
use rustc_span::MultiSpan;
use vir_crate::high::{self as vir, operations::ty::Typed};

pub struct TypeEncoder<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p Encoder<'v, 'tcx>,
    ty: ty::Ty<'tcx>,
}

impl<'p, 'v, 'r: 'v, 'tcx: 'v> TypeEncoder<'p, 'v, 'tcx> {
    pub fn new(encoder: &'p Encoder<'v, 'tcx>, ty: ty::Ty<'tcx>) -> Self {
        TypeEncoder { encoder, ty }
    }

    fn encode_substs(&self, substs: rustc_middle::ty::subst::SubstsRef<'tcx>) -> Vec<vir::Type> {
        substs
            .iter()
            .filter_map(|kind| {
                if let ty::subst::GenericArgKind::Type(ty) = kind.unpack() {
                    self.encoder.encode_type_high(ty).ok()
                } else {
                    None
                }
            })
            .collect()
    }

    fn encode_enum_name(&self, did: DefId) -> String {
        format!("enum${}", self.encoder.encode_item_name(did))
    }

    fn encode_union_name(&self, did: DefId) -> String {
        format!("union${}", self.encoder.encode_item_name(did))
    }

    fn encode_closure_name(&self, did: DefId) -> String {
        format!("closure${}", self.encoder.encode_item_name(did))
    }

    fn encode_function_def_name(&self, did: DefId) -> String {
        format!("fndef${}", self.encoder.encode_item_name(did))
    }

    fn is_mathematical_type(&self, did: DefId) -> bool {
        let type_name: &str = &self.encoder.env().tcx().def_path_str(did);
        matches!(type_name, "prusti_contracts::Seq" | "prusti_contracts::Map" | "prusti_contracts::Int")
    }

    fn compute_array_len(&self, size: ty::Const<'tcx>) -> u64 {
        self.encoder
            .const_eval_intlike(size.val())
            .unwrap()
            .to_u64()
            .unwrap()
    }

    pub fn encode_type(self) -> SpannedEncodingResult<vir::Type> {
        debug!("Encode type '{:?}'", self.ty);
        // self.encode_polymorphic_predicate_use()
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

            ty::TyKind::Ref(region, ty, mutability) => {
                let lft_name = region.to_text();
                let lifetime = vir::ty::LifetimeConst { name: lft_name };
                let uniqueness = self.encode_uniqueness(*mutability);
                vir::Type::reference(lifetime, uniqueness, self.encoder.encode_type_high(*ty)?)
            }

            ty::TyKind::Adt(adt_def, substs) if adt_def.is_struct() => {
                let type_name: &str = &self.encoder.env().tcx().def_path_str(adt_def.did());

                let enc_substs = self
                    .encode_substs(substs)
                    .into_iter()
                    .map(Box::new)
                    .collect::<Vec<_>>();

                // TODO: more stable reference to the Sequence type
                if type_name == "prusti_contracts::Seq" {
                    vir::Type::Sequence(vir::ty::Sequence {
                        element_type: enc_substs[0].clone(),
                    })
                } else if type_name == "prusti_contracts::Map" {
                    vir::Type::Map(vir::ty::Map {
                        key_type: enc_substs[0].clone(),
                        val_type: enc_substs[1].clone(),
                    })
                } else if type_name == "prusti_contracts::Int" {
                    vir::Type::Int(vir::ty::Int::Unbounded)
                } else {
                    vir::Type::struct_(
                        encode_struct_name(self.encoder, adt_def.did()),
                        self.encode_substs(substs),
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
                    )
                } else {
                    vir::Type::enum_(
                        self.encode_enum_name(adt_def.did()),
                        self.encode_substs(substs),
                        None,
                    )
                }
            }

            ty::TyKind::Adt(adt_def, substs) if adt_def.is_union() => vir::Type::union_(
                self.encode_union_name(adt_def.did()),
                self.encode_substs(substs),
                None,
            ),

            ty::TyKind::Adt(_adt_def, _substs) => {
                unreachable!();
            }

            ty::TyKind::Tuple(elems) => vir::Type::tuple(
                elems
                    .iter()
                    .filter_map(|ty| self.encoder.encode_type_high(ty).ok())
                    .collect(),
            ),

            ty::TyKind::Never => vir::Type::Never,

            ty::TyKind::Str => vir::Type::Str,

            ty::TyKind::Array(elem_ty, size) => {
                let array_len = self.compute_array_len(*size);
                vir::Type::array(array_len, self.encoder.encode_type_high(*elem_ty)?)
            }

            ty::TyKind::Slice(elem_ty) => {
                vir::Type::slice(self.encoder.encode_type_high(*elem_ty)?)
            }

            ty::TyKind::Closure(def_id, _substs) => vir::Type::closure(
                self.encode_closure_name(*def_id),
                // FIXME: We are currently ignoring type arguments.
                // self.encode_substs(substs),
            ),

            ty::TyKind::FnDef(def_id, _substs) => vir::Type::function_def(
                self.encode_function_def_name(*def_id),
                // FIXME: We are currently ignoring type arguments.
                // self.encode_substs(substs),
            ),

            ty::TyKind::Param(param_ty) => {
                vir::Type::TypeVar(self.encoder.encode_param(param_ty.name, param_ty.index))
            }

            ty::TyKind::Projection(ty::ProjectionTy {
                item_def_id,
                substs,
            }) => vir::Type::projection(
                self.encoder.encode_item_name(*item_def_id),
                self.encode_substs(substs),
            ),

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
            | ty::TyKind::Never
            | ty::TyKind::Tuple(_)
            | ty::TyKind::Projection(_)
            | ty::TyKind::Param(_)
            | ty::TyKind::Bound(..)
            | ty::TyKind::Placeholder(_)
            | ty::TyKind::Infer(_)
            | ty::TyKind::Error(_) => MultiSpan::new(),
            ty::TyKind::Adt(adt, _) => self.encoder.env().get_def_span(adt.did()).into(),
            ty::TyKind::Foreign(did)
            | ty::TyKind::FnDef(did, _)
            | ty::TyKind::Closure(did, _)
            | ty::TyKind::Generator(did, _, _)
            | ty::TyKind::Opaque(did, _) => self.encoder.env().get_def_span(*did).into(),
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
            ty::TyKind::Char => Some((0.into(), std::char::MAX.into())),
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

    pub fn encode_type_def(self) -> SpannedEncodingResult<vir::TypeDecl> {
        debug!("Encode type predicate '{:?}'", self.ty);
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
                        lower_bound = Some(Box::new(0usize.into()));
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
            ty::TyKind::RawPtr(rustc_middle::ty::TypeAndMut { ty, mutbl: _ }) => {
                let target_type = self.encoder.encode_type_high(*ty)?;
                vir::TypeDecl::pointer(target_type)
            }
            ty::TyKind::Ref(_, ty, mutability) => {
                let target_type = self.encoder.encode_type_high(*ty)?;
                vir::TypeDecl::reference(self.encode_uniqueness(*mutability), target_type)
            }
            ty::TyKind::Tuple(elems) => vir::TypeDecl::tuple(
                elems
                    .into_iter()
                    .filter_map(|ty| self.encoder.encode_type_high(ty).ok())
                    .collect(),
            ),
            ty::TyKind::Adt(adt_def, substs) if self.is_mathematical_type(adt_def.did()) => {
                let type_name: &str = &self.encoder.env().tcx().def_path_str(adt_def.did());
                let enc_substs = self.encode_substs(substs).into_iter().collect::<Vec<_>>();
                match type_name {
                    "prusti_contracts::Seq" => vir::TypeDecl::Sequence(vir::type_decl::Sequence {
                        element_type: enc_substs[0].clone(),
                    }),
                    "prusti_contracts::Map" => vir::TypeDecl::Map(vir::type_decl::Map {
                        key_type: enc_substs[0].clone(),
                        val_type: enc_substs[1].clone(),
                    }),
                    "prusti_contracts::Int" => vir::TypeDecl::Int(vir::type_decl::Int {
                        lower_bound: None,
                        upper_bound: None,
                    }),
                    _ => {
                        unreachable!();
                    }
                }
            }
            ty::TyKind::Adt(adt_def, substs) => {
                encode_adt_def(self.encoder, *adt_def, substs, None)?
            }
            ty::TyKind::Never => vir::TypeDecl::never(),
            ty::TyKind::Param(param_ty) => {
                vir::TypeDecl::type_var(vir_crate::high::type_decl::TypeVar::GenericType(
                    vir_crate::high::type_decl::GenericType {
                        name: param_ty.name.as_str().to_string(),
                    },
                ))
            }
            ty::TyKind::Closure(def_id, internal_substs) => {
                let cl_substs = internal_substs.as_closure();
                let arguments = cl_substs
                    .upvar_tys()
                    .filter_map(|ty| self.encoder.encode_type_high(ty).ok())
                    .collect();
                let name = self.encode_closure_name(*def_id);
                vir::TypeDecl::closure(name, arguments)
            }
            ty::TyKind::Array(elem_ty, size) => {
                let array_len = self.compute_array_len(*size);
                vir::TypeDecl::array(array_len, self.encoder.encode_type_high(*elem_ty)?)
            }
            ref ty_variant => {
                debug!("Encoding of type '{:?}' is incomplete", ty_variant);
                let ty = self.encoder.encode_type_high(self.ty)?;
                vir::TypeDecl::unsupported(ty)
            }
        };
        Ok(type_decl)
    }

    pub fn encode_predicate_use(self) -> EncodingResult<String> {
        let typ = self.encoder.encode_type(self.ty)?;
        Ok(typ.encode_as_string())
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
    //                 .const_eval_intlike(&size.val)
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

    pub fn encode_invariant_def(self, invariant_name: &str) -> EncodingResult<vir::FunctionDecl> {
        debug!("[enter] encode_invariant_def({:?})", self.ty);

        // let predicate_name = self.encoder.encode_type_predicate_use(self.ty)?;
        // let self_local_var = vir_local!{ self: {vir::Type::TypedRef(predicate_name.clone())} };

        // let invariant_name = self.encoder.encode_type_invariant_use(self.ty)?;

        // let field_invariants = match self.ty.kind() {
        //     ty::TyKind::Ref(_, ref ty, _) => {
        //         let elem_field = self.encoder.encode_dereference_field(ty)?;
        //         let elem_loc = vir::Expression::from(self_local_var.clone()).field(elem_field);
        //         Some(vec![
        //             self.encoder.encode_invariant_func_app(ty, elem_loc)?
        //         ])
        //     }

        //     ty::TyKind::Adt(ref adt_def, ref subst) if !adt_def.is_box() => {
        //         if self.is_supported_struct_type(adt_def, subst) {
        //             let own_substs =
        //                 ty::List::identity_for_item(self.encoder.env().tcx(), adt_def.did);

        //             // FIXME: this is a hack to support generics. See issue #187.
        //             let mut tymap = FxHashMap::default();

        //             for (kind1, kind2) in own_substs.iter().zip(*subst) {
        //                 if let (
        //                     ty::subst::GenericArgKind::Type(ty1),
        //                     ty::subst::GenericArgKind::Type(ty2),
        //                 ) = (kind1.unpack(), kind2.unpack())
        //                 {
        //                     tymap.insert(ty1, ty2);
        //                 }
        //             }
        //             let _cleanup_token = self.encoder.push_temp_tymap(tymap);

        //             let mut exprs: Vec<vir::Expression> = vec![];
        //             let num_variants = adt_def.variants().len();
        //             let tcx = self.encoder.env().tcx();

        //             let specs: Vec<typed::SpecificationSet> = Vec::new();
        //             // FIXME: type invariants need to be collected separately
        //             // in `SpecCollector`, and encoder should get a
        //             // `get_struct_specs` method or similar.
        //             // `get_procedure_specs` now only returns procedure specs,
        //             // so the match below for `SpecSet::Struct` would never
        //             // succeed.

        //             //if let Some(spec) = self.encoder.get_procedure_specs(adt_def.did) {
        //             //    specs.push(spec);
        //             //}

        //             // let traits = self.encoder.env().get_traits_decls_for_type(&self.ty);
        //             // for trait_id in traits {
        //             //     //if let Some(spec) = self.encoder.get_procedure_specs(trait_id) {
        //             //     //    specs.push(spec);
        //             //     //}
        //             // }

        //             for spec in specs.into_iter() {
        //                 //let encoded_args = vec![vir::Expression::from(self_local_var.clone())];
        //                 // let mut hacky_folder = HackyExprFolder {
        //                 //     saelf: self_local_var.clone(),
        //                 // };

        //                 match spec {
        //                     typed::SpecificationSet::Struct(items) => {
        //                         for _item in items {
        //                             // let enc = encode_simple_spec_assertion(
        //                             //     self.encoder,
        //                             //     &[],
        //                             //     &item.assertion
        //                             // );
        //                             let _enc = unimplemented!(
        //                                 "TODO: type invariants need to be upgraded \
        //                                 to the new compiler version"
        //                             );
        //                             // OPEN TODO: hacky fix here to convert the closure var to "self"...
        //                             // let enc = hacky_folder.fold(enc);
        //                             // exprs.push(enc);
        //                         }
        //                     }
        //                     _ => unreachable!(),
        //                 }
        //             }

        //             if num_variants == 0 {
        //                 debug!("ADT {:?} has no variant", adt_def);
        //                 // `false` here is currently unsound. See:
        //                 // * https://gitlab.inf.ethz.ch/OU-PMUELLER/prusti-dev/issues/158
        //                 // * https://gitlab.inf.ethz.ch/OU-PMUELLER/prusti-dev/issues/146
        //                 //exprs.push(false.into());
        //             } else if num_variants == 1 && (adt_def.is_struct() || adt_def.is_union()) {
        //                 debug!("ADT {:?} has only one variant", adt_def);

        //                 for field in &adt_def.non_enum_variant().fields {
        //                     debug!("Encoding field {:?}", field);
        //                     let field_name = &field.ident.as_str();
        //                     let field_ty = field.ty(tcx, subst);
        //                     let elem_field = self.encoder.encode_struct_field(field_name, field_ty)?;
        //                     let elem_loc =
        //                         vir::Expression::from(self_local_var.clone()).field(elem_field);
        //                     exprs.push(
        //                         self.encoder.encode_invariant_func_app(
        //                             field_ty,
        //                             elem_loc
        //                         )?
        //                     );
        //                 }
        //             } else {
        //                 debug!("ADT {:?} has {} variants", adt_def, num_variants);
        //                 // TODO: https://gitlab.inf.ethz.ch/OU-PMUELLER/prusti-dev/issues/201
        //             }

        //             Some(exprs)
        //         } else {
        //             // TODO: https://gitlab.inf.ethz.ch/OU-PMUELLER/prusti-dev/issues/201
        //             Some(vec![])
        //         }
        //     }

        //     // TODO
        //     _ => Some(vec![]),
        // };

        // let precondition = match self.ty.kind() {
        //     ty::TyKind::RawPtr(ty::TypeAndMut { ref ty, .. })
        //     | ty::TyKind::Ref(_, ref ty, _) => {
        //         // This is a reference, so we need to have it already unfolded.
        //         let elem_field = self.encoder.encode_dereference_field(ty)?;
        //         let elem_loc = vir::Expression::from(self_local_var.clone()).field(elem_field);
        //         vir::Expression::and(
        //             vir::Expression::acc_permission(elem_loc.clone(), vir::PermAmount::Read),
        //             vir::Expression::pred_permission(elem_loc, vir::PermAmount::Read).unwrap(),
        //         )
        //     }
        //     _ => vir::Expression::predicate_access_predicate(
        //         predicate_name,
        //         self_local_var.clone().into(),
        //         vir::PermAmount::Read,
        //     ),
        // };

        // let mut function = vir::Function {
        //     name: invariant_name,
        //     formal_args: vec![self_local_var],
        //     return_type: vir::Type::Bool,
        //     pres: vec![precondition],
        //     posts: Vec::new(),
        //     body: field_invariants.map(|invs| invs.into_iter().conjoin()),
        // };

        // // Patch snapshots
        // let function = self.encoder.patch_snapshots_function(function)?;

        // self.encoder
        //     .log_vir_program_before_foldunfold(function.to_string());

        // // Add folding/unfolding
        // let final_function = foldunfold::add_folding_unfolding_to_function(
        //     function,
        //     self.encoder.get_used_viper_predicates_map(),
        // ).unwrap(); // TODO: generate a stub function in case of error
        // debug!(
        //     "[exit] encode_invariant_def({:?}):\n{}",
        //     self.ty, final_function
        // );
        // Ok(final_function)

        // FIXME: Type invariants are currently not supported. To reenable them,
        // we need make them to use the regular function encoding mechanism with
        // snapshots. However, that mechanism is currently very hacky and needs
        // proper refactoring, which is blocked by VIR 2.0.
        let typ = self.encoder.encode_type_high(self.ty)?;
        let self_local_var = vir::VariableDecl::new("self", typ);
        Ok(vir::FunctionDecl {
            name: invariant_name.to_string(),
            type_arguments: Vec::new(), // FIXME: This is probably wrong.
            parameters: vec![self_local_var],
            return_type: vir::Type::Bool,
            pres: Vec::new(),
            posts: Vec::new(),
            body: Some(true.into()),
        })
    }

    // pub fn encode_invariant_use(self) -> EncodingResult<String> {
    //     debug!("Encode type invariant name '{:?}'", self.ty);
    //     Ok(format!("{}$inv", self.encode_predicate_use()?))
    // }

    pub fn encode_tag_def(self) -> vir::FunctionDecl {
        debug!("Encode type invariant '{:?}'", self.ty);

        //let pred_name = self.encoder.encode_type_tag_use(self.ty);
        //let self_local_var = vir::LocalVar::new("self", vir::Type::TypedRef(predicate_name.clone()));

        let tag_name = self.encoder.encode_type_tag_use(self.ty);

        let body = match self.ty.kind() {
            ty::TyKind::Param(_param_ty) => None,
            _ => {
                // FIXME: This looks very fishy!!!
                // It relies on the implementation detail that each `ty::TyS` instance has its own
                // `TyKind` instance; not an interned one.
                let value = self.ty.kind() as *const _ as usize;
                Some(value.into())
            }
        };

        //let precondition = vir::Expression::PredicateAccessPredicate(
        //    predicate_name,
        //    vec![self_local_var.clone().into()],
        //    vir::PermAmount::Write,
        //);

        vir::FunctionDecl {
            name: tag_name,
            type_arguments: Vec::new(), // FIXME: This is probably wrong.
            parameters: Vec::new(),
            return_type: vir::Type::Int(vir::ty::Int::Unbounded),
            pres: Vec::new(),
            posts: Vec::new(),
            body,
        }

        //// Add folding/unfolding
        //foldunfold::add_folding_unfolding_to_function(
        //    function,
        //    self.encoder.get_used_viper_predicates_map()
        //)
    }

    pub fn encode_tag_use(self) -> EncodingResult<String> {
        debug!("Encode type tag name '{:?}'", self.ty);
        Ok(format!("{}$tag", self.encode_predicate_use()?))
    }

    fn encode_uniqueness(&self, mutability: mir::Mutability) -> vir::ty::Uniqueness {
        match mutability {
            mir::Mutability::Mut => vir::ty::Uniqueness::Unique,
            mir::Mutability::Not => vir::ty::Uniqueness::Shared,
        }
    }
}

fn encode_box_name() -> String {
    "box$".to_string()
}

fn encode_struct_name<'v, 'tcx: 'v>(encoder: &Encoder<'v, 'tcx>, did: DefId) -> String {
    format!("struct${}", encoder.encode_item_name(did))
}

fn encode_variant<'v, 'tcx: 'v>(
    encoder: &Encoder<'v, 'tcx>,
    name: String,
    substs: ty::subst::SubstsRef<'tcx>,
    variant: &ty::VariantDef,
) -> SpannedEncodingResult<vir::type_decl::Struct> {
    let tcx = encoder.env().tcx();
    let mut fields = Vec::new();
    for field in &variant.fields {
        let field_name = crate::encoder::encoder::encode_field_name(field.ident(tcx).as_str());
        let field_ty = field.ty(tcx, substs);
        let field = vir::FieldDecl::new(field_name, encoder.encode_type_high(field_ty)?);
        fields.push(field);
    }
    let variant = vir::type_decl::Struct::new(name, fields);
    Ok(variant)
}

pub(super) fn encode_adt_def<'v, 'tcx>(
    encoder: &Encoder<'v, 'tcx>,
    adt_def: ty::AdtDef<'tcx>,
    substs: ty::subst::SubstsRef<'tcx>,
    variant_index: Option<rustc_target::abi::VariantIdx>,
) -> SpannedEncodingResult<vir::TypeDecl> {
    let tcx = encoder.env().tcx();
    if adt_def.is_box() {
        debug!("ADT {:?} is a box", adt_def);
        assert!(variant_index.is_none());
        let boxed_ty = encoder.encode_type_high(substs.type_at(0))?;
        let field = vir::FieldDecl::new("val_ref", boxed_ty);
        Ok(vir::TypeDecl::struct_(encode_box_name(), vec![field]))
    } else if adt_def.is_struct() {
        debug!("ADT {:?} is a struct", adt_def);
        assert!(variant_index.is_none());
        let name = encode_struct_name(encoder, adt_def.did());
        let variant = adt_def.non_enum_variant();
        Ok(vir::TypeDecl::Struct(encode_variant(
            encoder, name, substs, variant,
        )?))
    } else if adt_def.is_union() {
        debug!("ADT {:?} is a union", adt_def);
        if !config::unsafe_core_proof() {
            return Err(SpannedEncodingError::unsupported(
                "unions are not supported",
                encoder.env().get_def_span(adt_def.did()),
            ));
        }
        assert!(variant_index.is_none());
        let name = encode_struct_name(encoder, adt_def.did());
        // We treat union fields as variants.
        let variant = adt_def.non_enum_variant();
        let num_variants: i128 = variant.fields.len().try_into().unwrap();
        let discriminant_bounds = (0, num_variants - 1);
        let discriminant_values = (0..num_variants).collect();
        let mut variants = Vec::new();
        for field in &variant.fields {
            let field_name = field.ident(tcx).as_str().to_string();
            let field_ty = field.ty(tcx, substs);
            let encoded_field = vir::FieldDecl::new("value", encoder.encode_type_high(field_ty)?);
            let variant = vir::type_decl::Struct::new(field_name, vec![encoded_field]);
            variants.push(variant);
        }
        Ok(vir::TypeDecl::union_(
            name,
            vir::Type::Int(vir::ty::Int::Usize),
            vec![discriminant_bounds],
            discriminant_values,
            variants,
        ))
    } else if adt_def.is_enum() {
        debug!("ADT {:?} is an enum", adt_def);
        let name = encode_struct_name(encoder, adt_def.did());
        let num_variants = adt_def.variants().len();
        debug!("ADT {:?} is enum with {} variants", adt_def, num_variants);
        let type_decl = if num_variants == 1 {
            // FIXME: Currently fold-unfold assumes that everything that
            // has only a single variant is a struct.
            let variant = &adt_def.variants()[0usize.into()];
            vir::TypeDecl::Struct(encode_variant(encoder, name, substs, variant)?)
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
                let encoded_variant = encode_variant(encoder, name, substs, variant)?;
                variants.push(encoded_variant);
            }
            let mir_discriminant_type = match adt_def.repr().discr_type() {
                rustc_attr::IntType::SignedInt(int) => {
                    let int = match int {
                        rustc_ast::ast::IntTy::Isize => rustc_middle::ty::IntTy::Isize,
                        rustc_ast::ast::IntTy::I8 => rustc_middle::ty::IntTy::I8,
                        rustc_ast::ast::IntTy::I16 => rustc_middle::ty::IntTy::I16,
                        rustc_ast::ast::IntTy::I32 => rustc_middle::ty::IntTy::I32,
                        rustc_ast::ast::IntTy::I64 => rustc_middle::ty::IntTy::I64,
                        rustc_ast::ast::IntTy::I128 => rustc_middle::ty::IntTy::I128,
                    };
                    encoder.env().tcx().mk_ty(ty::TyKind::Int(int))
                }
                rustc_attr::IntType::UnsignedInt(uint) => {
                    let uint = match uint {
                        rustc_ast::ast::UintTy::Usize => rustc_middle::ty::UintTy::Usize,
                        rustc_ast::ast::UintTy::U8 => rustc_middle::ty::UintTy::U8,
                        rustc_ast::ast::UintTy::U16 => rustc_middle::ty::UintTy::U16,
                        rustc_ast::ast::UintTy::U32 => rustc_middle::ty::UintTy::U32,
                        rustc_ast::ast::UintTy::U64 => rustc_middle::ty::UintTy::U64,
                        rustc_ast::ast::UintTy::U128 => rustc_middle::ty::UintTy::U128,
                    };
                    encoder.env().tcx().mk_ty(ty::TyKind::Uint(uint))
                }
            };
            let discriminant_type = encoder.encode_type_high(mir_discriminant_type)?;
            vir::TypeDecl::enum_(
                name,
                discriminant_type,
                discriminant_bounds,
                discriminant_values,
                variants,
            )
        };
        Ok(type_decl)
    } else {
        Err(SpannedEncodingError::internal(
            format!("unexpected variant of adt_def: {:?}", adt_def),
            encoder.env().get_def_span(adt_def.did()),
        ))
    }
}
