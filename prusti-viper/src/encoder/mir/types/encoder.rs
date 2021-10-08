// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::{helpers::compute_discriminant_values, interface::MirTypeEncoderInterface};
use crate::encoder::{
    errors::{EncodingResult, SpannedEncodingError, SpannedEncodingResult},
    high::types::HighTypeEncoderInterface,
    mir::{
        generics::MirGenericsEncoderInterface, types::helpers::compute_discriminant_bounds_high,
        pure::SpecificationEncoderInterface,
        specifications::SpecificationsInterface,
    },
    snapshot::interface::SnapshotEncoderInterface,
    Encoder,
};
use log::debug;
use prusti_common::config;

use rustc_hir::def_id::DefId;
use rustc_middle::ty;
use rustc_span::MultiSpan;
use rustc_hash::FxHashMap;

use vir_crate::high::{self as vir};

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

    fn compute_array_len(&self, size: &ty::Const<'tcx>) -> u64 {
        self.encoder
            .const_eval_intlike(&size.val)
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
                vir::Type::pointer(self.encoder.encode_type_high(ty)?)
            }

            ty::TyKind::Ref(_, ty, _) => vir::Type::reference(self.encoder.encode_type_high(ty)?),

            ty::TyKind::Adt(adt_def, substs) if adt_def.is_struct() => vir::Type::struct_(
                encode_struct_name(self.encoder, adt_def.did),
                self.encode_substs(substs),
            ),

            ty::TyKind::Adt(adt_def, substs) if adt_def.is_enum() => {
                if adt_def.variants.len() == 1 {
                    // FIXME: Currently fold-unfold assumes that everything that
                    // has only a single variant is a struct.
                    vir::Type::struct_(
                        encode_struct_name(self.encoder, adt_def.did),
                        self.encode_substs(substs),
                    )
                } else {
                    vir::Type::enum_(
                        self.encode_enum_name(adt_def.did),
                        self.encode_substs(substs),
                        None,
                    )
                }
            }

            ty::TyKind::Adt(adt_def, substs) if adt_def.is_union() => vir::Type::union_(
                self.encode_union_name(adt_def.did),
                self.encode_substs(substs),
            ),

            ty::TyKind::Adt(_adt_def, _substs) => {
                unreachable!();
            }

            ty::TyKind::Tuple(elems) => vir::Type::tuple(
                elems
                    .iter()
                    .filter_map(|ty| self.encoder.encode_type_high(ty.expect_ty()).ok())
                    .collect(),
            ),

            ty::TyKind::Never => vir::Type::Never,

            ty::TyKind::Str => vir::Type::Str,

            ty::TyKind::Array(elem_ty, size) => {
                let array_len = self.compute_array_len(size);
                vir::Type::array(array_len, self.encoder.encode_type_high(elem_ty)?)
            }

            ty::TyKind::Slice(elem_ty) => vir::Type::slice(self.encoder.encode_type_high(elem_ty)?),

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
            ty::TyKind::Adt(adt, _) => self.encoder.env().get_def_span(adt.did).into(),
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
                let bounds = match int_ty {
                    ty::IntTy::I8 => (std::i8::MIN.into(), std::i8::MAX.into()),
                    ty::IntTy::I16 => (std::i16::MIN.into(), std::i16::MAX.into()),
                    ty::IntTy::I32 => (std::i32::MIN.into(), std::i32::MAX.into()),
                    ty::IntTy::I64 => (std::i64::MIN.into(), std::i64::MAX.into()),
                    ty::IntTy::I128 => (std::i128::MIN.into(), std::i128::MAX.into()),
                    ty::IntTy::Isize => (std::isize::MIN.into(), std::isize::MAX.into()),
                };
                Some(bounds)
            }
            ty::TyKind::Uint(uint_ty) => {
                let bounds = match uint_ty {
                    ty::UintTy::U8 => (0.into(), std::u8::MAX.into()),
                    ty::UintTy::U16 => (0.into(), std::u16::MAX.into()),
                    ty::UintTy::U32 => (0.into(), std::u32::MAX.into()),
                    ty::UintTy::U64 => (0.into(), std::u64::MAX.into()),
                    ty::UintTy::U128 => (0.into(), std::u128::MAX.into()),
                    ty::UintTy::Usize => (0.into(), std::usize::MAX.into()),
                };
                Some(bounds)
            }
            ty::TyKind::Char => Some((0.into(), std::char::MAX.into())),
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
                        lower_bound = Some(Box::new(0.into()));
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
            ty::TyKind::Ref(_, ty, _) => {
                let target_type = self.encoder.encode_type_high(ty)?;
                vir::TypeDecl::reference(target_type)
            }
            ty::TyKind::Tuple(elems) => vir::TypeDecl::tuple(
                elems
                    .iter()
                    .filter_map(|ty| self.encoder.encode_type_high(ty.expect_ty()).ok())
                    .collect(),
            ),
            ty::TyKind::Adt(adt_def, substs) => {
                encode_adt_def(self.encoder, adt_def, substs, None)?
            }
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
                let name = self.encode_closure_name(*def_id);
                vir::TypeDecl::closure(name, arguments)
            }
            ty::TyKind::Array(elem_ty, size) => {
                let array_len = self.compute_array_len(size);
                vir::TypeDecl::array(array_len, self.encoder.encode_type_high(elem_ty)?)
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
    //                 .filter_map(|ty| self.encoder.encode_type(ty.expect_ty()).ok())
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

    pub fn encode_invariant_def(self, invariant_name: &str) -> EncodingResult<vir_crate::polymorphic::Function> {
        use prusti_common::vir_local;
        use vir_crate::polymorphic::{self as vir};
        use vir_crate::polymorphic::ExprIterator;

        debug!("[enter] encode_invariant_def({:?})", self.ty);

        let typ = self.encoder.encode_type(self.ty)?;
        let predicate_name = typ.encode_as_string();
        let self_local_var = vir_local! { self: {typ.clone() } };

        let field_invariants = match self.ty.kind() {
            ty::TyKind::Ref(_, ref ty, _) if should_encode_typ_invariant(ty) => {
                let elem_field = self.encoder.encode_dereference_field(ty)?;
                let elem_loc = vir::Expr::from(self_local_var.clone()).field(elem_field);
                Some(vec![self
                    .encoder
                    .encode_invariant_func_app(ty, elem_loc)?])
            }
            ty::TyKind::Adt(ref adt_def, ref subst) if !adt_def.is_box() => {
                let mut exprs: Vec<vir::Expr> = vec![];
                let num_variants = adt_def.variants.len();
                let tcx = self.encoder.env().tcx();
                if let Some(spec) = self.encoder.get_struct_specs(adt_def.did) {
                    for assertion in spec.invariant.extract_with_selective_replacement_iter() {
                        let enc = self.encoder.encode_assertion(
                            assertion,
                            None,
                            &vec![], // TODO: self?
                            None,
                            true,
                            adt_def.did,
                            &FxHashMap::default(), // TODO: generics
                            &ty::List::empty(),
                        )?;
                        //let expr = (HackyExprFolder {saelf: self_local_var.clone()}).fold(enc.unwrap());
                        let expr = enc;
                        exprs.push(expr);
                    }
                    if num_variants == 0 {
                        debug!("ADT {:?} has no variant", adt_def);
                    } else if num_variants == 1 && (adt_def.is_struct() || adt_def.is_union()) {
                        debug!("ADT {:?} has only one variant", adt_def);
                        for field in &adt_def.non_enum_variant().fields {
                            debug!("Encoding field {:?}", field);
                            let field_name = field.ident(tcx).to_string();
                            let field_ty = field.ty(tcx, subst);
                            let elem_field = self.encoder.encode_struct_field(&field_name, field_ty)?;
                            let elem_loc = vir::Expr::from(self_local_var.clone()).field(elem_field);
                            exprs.push(self.encoder.encode_invariant_func_app(field_ty, elem_loc)?);
                        }
                    } else {
                        debug!("ADT {:?} has {} variants", adt_def, num_variants);
                        // TODO: https://gitlab.inf.ethz.ch/OU-PMUELLER/prusti-dev/issues/201
                    }
                }
                if num_variants > 1 {
                    let discriminant_field = self.encoder.encode_discriminant_field();
                    let discriminant_values = compute_discriminant_values(adt_def, tcx);
                    let discriminant_loc =
                        vir::Expr::from(self_local_var.clone()).field(discriminant_field.clone());
                    adt_def.variants.iter().zip(discriminant_values).for_each(
                        |(variant_def, variant_index)| {
                            let variant_name = variant_def.ident.to_string();
                            let variant_loc =
                                vir::Expr::from(self_local_var.clone()).variant(&variant_name);
                            let variant_predicate =
                                typ.clone().variant(&variant_name).encode_as_string();
                            let guard =
                                vir::Expr::eq_cmp(discriminant_loc.clone(), variant_index.into());
                            variant_def.fields.iter().for_each(|field| {
                                let field_name = field.ident.to_string();
                                let field_ty = field.ty(tcx, subst);
                                let vir_field = self
                                    .encoder
                                    .encode_struct_field(&field_name, field_ty)
                                    .unwrap();
                                let field_loc = variant_loc.clone().field(vir_field.clone());

                                // The appropriate invariant for the nested field
                                let invariant_expr = self
                                    .encoder
                                    .encode_invariant_func_app(field_ty, field_loc.clone())
                                    .unwrap();

                                // Unfold the variant predicate
                                let invariant_expr = vir::Expr::unfolding(
                                    variant_predicate.clone(),
                                    vec![variant_loc.clone()],
                                    invariant_expr,
                                    vir::PermAmount::Read,
                                    None,
                                );

                                // Make the variant accessible
                                let invariant_expr = vir::Expr::unfolding(
                                    predicate_name.clone(),
                                    vec![vir::Expr::from(self_local_var.clone())],
                                    invariant_expr,
                                    vir::PermAmount::Read,
                                    Some(vir::EnumVariantIndex::new(variant_name))
                                );
                                let implication = vir::Expr::implies(guard.clone(), invariant_expr);
                                exprs.push(implication);
                            });
                        },
                    );
                }
                Some(exprs)
            }
            _ => Some(vec![]),
        };

        let precondition = match self.ty.kind() {
            ty::TyKind::RawPtr(ty::TypeAndMut { ref ty, .. }) | ty::TyKind::Ref(_, ref ty, _) => {
                // This is a reference, so we need to have it already unfolded.
                let elem_field = self.encoder.encode_dereference_field(ty)?;
                let elem_loc = vir::Expr::from(self_local_var.clone()).field(elem_field);
                vir::Expr::and(
                    vir::Expr::acc_permission(elem_loc.clone(), vir::PermAmount::Read),
                    vir::Expr::pred_permission(elem_loc, vir::PermAmount::Read).unwrap(),
                )
            }
            _ => vir::Expr::predicate_access_predicate(
                self.encoder.encode_type(self.ty).unwrap(),
                self_local_var.clone().into(),
                vir::PermAmount::Read,
            ),
        };
        let function = vir::Function {
            name: self.encoder.encode_type_invariant_use(self.ty)?,
            type_arguments: vec![], // TODO: generics
            formal_args: vec![self_local_var],
            return_type: vir::Type::Bool,
            pres: vec![precondition],
            posts: vec![],
            body: field_invariants.map(|invs| invs.into_iter().conjoin()),
        };
        // // Patch snapshots
        let function = self
            .encoder
            .patch_snapshots_function(function, &FxHashMap::default())?;

        self.encoder
            .log_vir_program_before_foldunfold(function.to_string());

        let predicates_map = self.encoder.get_used_viper_predicates_map();

        // Add folding/unfolding
        let function = function; /* foldunfold::add_folding_unfolding_to_function(
            function,
            predicates_map
        ).unwrap(); // TODO: generate a stub function in case of error */
        debug!("[exit] encode_invariant_def({:?}):\n{}", self.ty, function);
        Ok(function)
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
                let value = self.ty as *const ty::TyS<'tcx> as usize;
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
    adt_def: &'tcx ty::AdtDef,
    substs: ty::subst::SubstsRef<'tcx>,
    variant_index: Option<rustc_target::abi::VariantIdx>,
) -> SpannedEncodingResult<vir::TypeDecl> {
    if adt_def.is_box() {
        debug!("ADT {:?} is a box", adt_def);
        assert!(variant_index.is_none());
        let boxed_ty = encoder.encode_type_high(substs.type_at(0))?;
        let field = vir::FieldDecl::new("val_ref", boxed_ty);
        Ok(vir::TypeDecl::struct_(encode_box_name(), vec![field]))
    } else if adt_def.is_struct() {
        debug!("ADT {:?} is a struct", adt_def);
        assert!(variant_index.is_none());
        let name = encode_struct_name(encoder, adt_def.did);
        let variant = adt_def.non_enum_variant();
        Ok(vir::TypeDecl::Struct(encode_variant(
            encoder, name, substs, variant,
        )?))
    } else if adt_def.is_union() {
        debug!("ADT {:?} is a union", adt_def);
        assert!(variant_index.is_none());
        Err(SpannedEncodingError::unsupported(
            "unions are not supported",
            encoder.env().get_def_span(adt_def.did),
        ))
    } else if adt_def.is_enum() {
        debug!("ADT {:?} is an enum", adt_def);
        let name = encode_struct_name(encoder, adt_def.did);
        let num_variants = adt_def.variants.len();
        debug!("ADT {:?} is enum with {} variants", adt_def, num_variants);
        let type_decl = if num_variants == 1 {
            // FIXME: Currently fold-unfold assumes that everything that
            // has only a single variant is a struct.
            let variant = &adt_def.variants[0usize.into()];
            vir::TypeDecl::Struct(encode_variant(encoder, name, substs, variant)?)
        } else if let Some(_variant_index) = variant_index {
            // let variant = &adt_def.variants[variant_index];
            // vir::TypeDecl::Struct(encode_variant(encoder, name, substs, variant)?)
            unimplemented!("FIXME: How this should be implemented?")
        } else {
            let tcx = encoder.env().tcx();
            let discriminant = vir::Expression::discriminant();
            let discriminant_bounds = compute_discriminant_bounds_high(adt_def, tcx, &discriminant);
            let discriminant_values = compute_discriminant_values(adt_def, tcx)
                .into_iter()
                .map(|value| value.into())
                .collect();
            let mut variants = Vec::new();
            for variant in &adt_def.variants {
                let name = variant.ident(tcx).to_string();
                let encoded_variant = encode_variant(encoder, name, substs, variant)?;
                variants.push(encoded_variant);
            }
            vir::TypeDecl::enum_(name, discriminant_bounds, discriminant_values, variants)
        };
        Ok(type_decl)
    } else {
        Err(SpannedEncodingError::internal(
            format!("unexpected variant of adt_def: {:?}", adt_def),
            encoder.env().get_def_span(adt_def.did),
        ))
    }
}

fn should_encode_typ_invariant(ty: ty::Ty<'_>) -> bool {
    match ty.kind() {
        ty::TyKind::Ref(_, ty, _) => should_encode_typ_invariant(ty),
        ty::TyKind::Adt(ref adt_def, _) => !adt_def.is_box(),
        _ => false,
    }
}
