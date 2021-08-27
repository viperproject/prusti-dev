// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::foldunfold;
use crate::encoder::utils::range_extract;
use crate::encoder::utils::PlusOne;
use crate::encoder::Encoder;
use prusti_common::{config, vir_local};
use vir_crate::polymorphic::{self as vir, ExprFolder, ExprIterator};
// use prusti_interface::specifications::*;
// use rustc::middle::const_val::ConstVal;
use rustc_middle::ty;
use rustc_target::abi;
use rustc_middle::ty::layout::IntegerExt;
// use rustc_data_structures::indexed_vec::Idx;
// use std;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use prusti_interface::specs::typed;
use rustc_attr::IntType::SignedInt;
use rustc_target::abi::Integer;
use log::{debug, trace};
use crate::encoder::errors::{EncodingError, EncodingResult};
use crate::encoder::builtin_encoder::BuiltinFunctionKind;
use std::convert::TryInto;

pub struct TypeEncoder<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p Encoder<'v, 'tcx>,
    ty: ty::Ty<'tcx>,
}

impl<'p, 'v, 'r: 'v, 'tcx: 'v> TypeEncoder<'p, 'v, 'tcx> {
    pub fn new(encoder: &'p Encoder<'v, 'tcx>, ty: ty::Ty<'tcx>) -> Self {
        TypeEncoder { encoder, ty }
    }

    pub fn encode_type(self) -> EncodingResult<vir::Type> {
        debug!("Encode type '{:?}'", self.ty);
        self.encode_polymorphic_predicate_use()
    }

    pub fn encode_value_field(self) -> EncodingResult<vir::Field> {
        trace!("Encode value field for type '{:?}'", self.ty);
        Ok(match self.ty.kind() {
            ty::TyKind::Bool => vir::Field::new("val_bool", vir::Type::Bool),

            ty::TyKind::Int(_) | ty::TyKind::Uint(_) | ty::TyKind::Char => {
                vir::Field::new("val_int", vir::Type::Int)
            }

            ty::TyKind::Ref(_, ref ty, _) => {
                let typ = self.encoder.encode_type(ty)?;
                vir::Field::new("val_ref", typ)
            }

            // For composed data structures, we typically use a snapshot rather than a field.
            // To unify how parameters are passed to functions, we treat them like a reference.
            ty::TyKind::Adt(_, _)
            | ty::TyKind::Tuple(_)
            | ty::TyKind::Closure(_, _)
            | ty::TyKind::FnDef(_, _) => {
                let typ = self.encoder.encode_type(self.ty)?;
                vir::Field::new("val_ref", typ)
            }

            ty::TyKind::RawPtr(ty::TypeAndMut { .. }) => {
                return Err(EncodingError::unsupported(
                    "raw pointers are not supported"
                ));
            }

            ty::TyKind::Array(..) => {
                return Err(EncodingError::internal(
                    "TypeEncoder::encode_value_field should not be called for arrays"
                ));
            }

            ty::TyKind::Float(_) => {
                return Err(EncodingError::unsupported(
                    "float type is not supported"
                ));
            }

            ty::TyKind::Foreign(_) => {
                return Err(EncodingError::unsupported(
                    "foreign function interface is not supported"
                ));
            }

            ty::TyKind::Str => {
                return Err(EncodingError::unsupported(
                    "strings are not supported"
                ));
            }

            ty::TyKind::Slice(_) => {
                return Err(EncodingError::unsupported(
                    "array slices are not supported"
                ));
            }

            ty::TyKind::FnPtr(_) => {
                return Err(EncodingError::unsupported(
                    "function pointers are not supported"
                ));
            }

            ty::TyKind::Dynamic(..) => {
                return Err(EncodingError::unsupported(
                    "trait objects are not supported"
                ));
            }

            ty::TyKind::Generator(..)
            | ty::TyKind::GeneratorWitness(..) => {
                return Err(EncodingError::unsupported(
                    "generators are not supported"
                ));
            }

            ty::TyKind::Never => {
                return Err(EncodingError::unsupported(
                    "never type is not supported"
                ));
            }

            ty::TyKind::Projection(_) => {
                return Err(EncodingError::unsupported(
                    "projections are not supported"
                ));
            }

            ty::TyKind::Opaque(_, _) => {
                return Err(EncodingError::unsupported(
                    "opaque types not supported"
                ));
            }

            ty::TyKind::Param(_) => {
                return Err(EncodingError::unsupported(
                    "type parameters in arrays are not supported"
                ));
            }

            ty::TyKind::Bound(_, _) => {
                return Err(EncodingError::unsupported(
                    "bound type variables are not supported"
                ));
            }

            ty::TyKind::Placeholder(_) => {
                return Err(EncodingError::unsupported(
                    "placeholder types are not supported"
                ));
            }

            ty::TyKind::Infer(_) => {
                return Err(EncodingError::unsupported(
                    "inference types are not supported"
                ));
            }

            ty::TyKind::Error(_) => {
                return Err(EncodingError::unsupported(
                    "error type is not supported"
                ));
            }
        })
    }

    fn get_integer_bounds(&self) -> Option<(vir::Expr, vir::Expr)> {
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
            ty::TyKind::Char => {
                Some((0.into(), std::char::MAX.into()))
            }
            ty::TyKind::Bool | ty::TyKind::Ref(_, _, _) => None,
            ref x => unreachable!("{:?}", x),
        }
    }

    pub fn encode_bounds(self, var: &vir::Expr) -> Vec<vir::Expr> {
        if let Some((lower, upper)) = self.get_integer_bounds() {
            vec![
                vir::Expr::le_cmp(lower, var.clone()),
                vir::Expr::le_cmp(var.clone(), upper),
            ]
        } else {
            Vec::new()
        }
    }

    pub fn encode_predicate_def(self) -> EncodingResult<Vec<vir::Predicate>> {
        debug!("Encode type predicate '{:?}'", self.ty);
        let typ = self.encoder.encode_type(self.ty)?;

        Ok(match self.ty.kind() {
            ty::TyKind::Bool => vec![vir::Predicate::new_primitive_value(
                typ,
                self.encoder.encode_value_field(self.ty)?,
                None,
                false,
            )],

            ty::TyKind::Int(_) | ty::TyKind::Uint(_) | ty::TyKind::Char => {
                let bounds = if config::check_overflows() {
                    self.get_integer_bounds()
                } else {
                    None
                };
                let unsigned = if let ty::TyKind::Uint(_) = self.ty.kind() {
                    config::encode_unsigned_num_constraint()
                } else {
                    false
                };
                vec![vir::Predicate::new_primitive_value(
                    typ,
                    self.encoder.encode_value_field(self.ty)?,
                    bounds,
                    unsigned,
                )]
            }

            ty::TyKind::Ref(_, ref ty, _) => {
                vec![vir::Predicate::new_struct(
                    typ,
                    vec![self.encoder.encode_dereference_field(ty)?],
                )]
            },

            ty::TyKind::Tuple(elems) => {
                let fields = elems
                    .iter()
                    .enumerate()
                    .map(|(field_num, ty)| {
                        let field_name = format!("tuple_{}", field_num);
                        self.encoder.encode_raw_ref_field(field_name, ty.expect_ty())
                    })
                    .collect::<Result<_, _>>()?;
                vec![vir::Predicate::new_struct(typ, fields)]
            }

            ty::TyKind::Adt(adt_def, subst) if !adt_def.is_box() => {
                let num_variants = adt_def.variants.len();
                let tcx = self.encoder.env().tcx();
                if num_variants == 1 {
                    debug!("ADT {:?} has only one variant", adt_def);
                    let mut fields = vec![];
                    for field in &adt_def.variants[0usize.into()].fields {
                        let field_name = field.ident.to_string();
                        let field_ty = field.ty(tcx, subst);
                        fields.push(
                            self.encoder.encode_struct_field(
                                &field_name,
                                field_ty
                            )?
                        );
                    }
                    vec![vir::Predicate::new_struct(typ, fields)]
                } else {
                    debug!("ADT {:?} has {} variants", adt_def, num_variants);
                    let discriminant_field = self.encoder.encode_discriminant_field();
                    let this = vir::Predicate::construct_this(typ.clone());
                    let discriminant_loc =
                        vir::Expr::from(this.clone()).field(discriminant_field.clone());
                    let discriminant_bounds =
                        compute_discriminant_bounds(adt_def, tcx, &discriminant_loc);

                    let discriminant_values = compute_discriminant_values(adt_def, tcx);
                    let variants: Vec<_> = adt_def
                        .variants
                        .iter()
                        .zip(discriminant_values)
                        .map(|(variant_def, variant_index)| {
                            let fields_res = variant_def
                                .fields
                                .iter()
                                .map(|field| {
                                    debug!("Encoding field {:?}", field);
                                    let field_name = &field.ident.as_str();
                                    let field_ty = field.ty(tcx, subst);
                                    self.encoder.encode_struct_field(field_name, field_ty)
                                })
                                .collect::<Result<_, _>>();
                            let variant_name = &variant_def.ident.as_str();
                            let guard = vir::Expr::eq_cmp(
                                discriminant_loc.clone().into(),
                                variant_index.into(),
                            );
                            let variant_typ = typ.clone().variant(variant_name);
                            fields_res.map(|fields| (
                                guard,
                                variant_name.to_string(),
                                vir::StructPredicate::new(variant_typ, fields),
                            ))
                        })
                        .collect::<Result<_, _>>()?;
                    for (_, name, _) in &variants {
                        self.encoder.encode_enum_variant_field(name);
                    }
                    let mut predicates: Vec<_> = variants
                        .iter()
                        .filter(|(_, _, predicate)| !predicate.has_empty_body())
                        .map(|(_, _, predicate)| vir::Predicate::Struct(predicate.clone()))
                        .collect();
                    let enum_predicate = vir::Predicate::new_enum(
                        this,
                        discriminant_field,
                        discriminant_bounds,
                        variants,
                    );
                    predicates.push(enum_predicate);
                    predicates
                }
            }

            ty::TyKind::Adt(ref adt_def, ref _subst) if adt_def.is_box() => {
                let num_variants = adt_def.variants.len();
                assert_eq!(num_variants, 1);
                let field_ty = self.ty.boxed_ty();
                vec![vir::Predicate::new_struct(
                    typ,
                    vec![self.encoder.encode_dereference_field(field_ty)?],
                )]
            }

            ty::TyKind::Never => {
                // FIXME: This should be a predicate with the body `false`. See issue #38.
                vec![vir::Predicate::new_abstract(typ)]
            }

            ty::TyKind::Param(_) => {
                // special case: type parameters shall be encoded as *abstract* predicates
                vec![vir::Predicate::new_abstract(typ)]
            }

            ty::TyKind::Closure(_def_id, internal_substs) => {
                let closure_substs = internal_substs.as_closure();
                match closure_substs.tupled_upvars_ty().kind() {
                    ty::TyKind::Tuple(_upvar_substs) => {
                        // TODO: this should encode the state of a closure, i.e.
                        // the "self" parameter passed into the implementation
                        // function generated for every closure. This should
                        // work using snapshots. For now, the "self" parameter
                        // is skipped in encoding.

                        // let field_name = "upvars".to_owned();
                        // let field = self.encoder.encode_raw_ref_field(field_name, cl_upvars);
                        // let pred = vir::Predicate::new_struct(typ, vec![field.clone()]);
                        let pred = vir::Predicate::new_struct(typ.clone(), vec![]);
                        // trace!("Encoded closure type {:?} as {:?} with field {:?}", typ, pred, field);
                        trace!("Encoded closure type {:?} as {:?}", typ, pred);
                        vec![pred]
                    }

                    _ => unreachable!()
                }
            }

            ty::TyKind::Array(..) => {
                vec![
                    vir::Predicate::new_abstract(typ),
                ]
            }

            ref ty_variant => {
                debug!("Encoding of type '{:?}' is incomplete", ty_variant);
                vec![vir::Predicate::new_abstract(typ)]
            }
        })
    }

    pub fn encode_predicate_use(self) -> EncodingResult<String> {
        let typ = self.encoder.encode_type(self.ty)?;
        Ok(typ.encode_as_string())
    }

    fn encode_polymorphic_predicate_use(self) -> EncodingResult<vir::Type> {
        debug!("Encode type predicate name '{:?}'", self.ty);

        let result = match self.ty.kind() {
            ty::TyKind::Bool => vir::Type::typed_ref("bool"),

            ty::TyKind::Int(ty::IntTy::I8) => vir::Type::typed_ref("i8"),
            ty::TyKind::Int(ty::IntTy::I16) => vir::Type::typed_ref("i16"),
            ty::TyKind::Int(ty::IntTy::I32) => vir::Type::typed_ref("i32"),
            ty::TyKind::Int(ty::IntTy::I64) => vir::Type::typed_ref("i64"),
            ty::TyKind::Int(ty::IntTy::I128) => vir::Type::typed_ref("i128"),
            ty::TyKind::Int(ty::IntTy::Isize) => vir::Type::typed_ref("isize"),

            ty::TyKind::Uint(ty::UintTy::U8) => vir::Type::typed_ref("u8"),
            ty::TyKind::Uint(ty::UintTy::U16) => vir::Type::typed_ref("u16"),
            ty::TyKind::Uint(ty::UintTy::U32) => vir::Type::typed_ref("u32"),
            ty::TyKind::Uint(ty::UintTy::U64) => vir::Type::typed_ref("u64"),
            ty::TyKind::Uint(ty::UintTy::U128) => vir::Type::typed_ref("u128"),
            ty::TyKind::Uint(ty::UintTy::Usize) => vir::Type::typed_ref("usize"),

            ty::TyKind::Char => vir::Type::typed_ref("char"),

            ty::TyKind::RawPtr(ty::TypeAndMut { ref ty, .. }) => {
                vir::Type::typed_ref_with_args("raw_ref", vec![self.encoder.encode_type(ty)?])
            }
            ty::TyKind::Ref(_, ref ty, _) => {
                vir::Type::typed_ref_with_args("ref", vec![self.encoder.encode_type(ty)?])
            }

            ty::TyKind::Adt(adt_def, subst) => {
                vir::Type::typed_ref_with_args(format!("adt${}", self.encoder.encode_item_name(adt_def.did)), subst.iter().filter_map(|kind|
                    if let ty::subst::GenericArgKind::Type(ty) = kind.unpack() {
                        self.encoder.encode_type(ty).map_or(None, |val| Some(val))
                    } else {
                        None
                    }
                ).collect())
            }

            ty::TyKind::Tuple(elems) => {
                vir::Type::typed_ref_with_args("tuple", elems.iter().filter_map(|ty|
                    self.encoder.encode_type(ty.expect_ty()).map_or(None, |val|Some(val))
                ).collect())
            }

            ty::TyKind::Never => vir::Type::typed_ref("never"),

            ty::TyKind::Str => vir::Type::typed_ref("str"),

            ty::TyKind::Array(elem_ty, size) => {
                let array_len =
                    self.encoder
                        .const_eval_intlike(&size.val).unwrap()
                        .to_u64().unwrap();
                vir::Type::typed_ref_with_args(format!("Array${}", array_len), vec![self.encoder.encode_type(elem_ty)?])
            }

            ty::TyKind::Slice(elem_ty) => {
                vir::Type::typed_ref_with_args("Slice", vec![self.encoder.encode_type(elem_ty)?])
            }

            ty::TyKind::Closure(def_id, closure_subst) => {
                vir::Type::typed_ref_with_args(
                    format!("closure${}_{}", def_id.krate.as_u32(), def_id.index.as_u32()), 
                    closure_subst.iter().filter_map(|kind|
                        if let ty::subst::GenericArgKind::Type(ty) = kind.unpack() {
                            self.encoder.encode_type(ty).map_or(None, |val| Some(val))
                        } else {
                            None
                        }
                    ).collect()
                )
            }

            ty::TyKind::Param(param_ty) => {
                vir::Type::type_var(format!("{}", param_ty.name.as_str()))
            }

            ty::TyKind::Projection(ty::ProjectionTy { item_def_id, substs }) => {
                vir::Type::typed_ref_with_args(self.encoder.encode_item_name(*item_def_id), substs.iter().filter_map(|kind|
                    if let ty::subst::GenericArgKind::Type(ty) = kind.unpack() {
                        self.encoder.encode_type(ty).map_or(None, |val| Some(val))
                    } else {
                        None
                    }
                ).collect())
            }

            ty::TyKind::Dynamic(..) => {
                vir::Type::typed_ref("unsupported$dynamic")
            }

            ty::TyKind::FnPtr(..) => {
                vir::Type::typed_ref("unsupported$fnptr")
            }

            ty::TyKind::FnDef(..) => {
                vir::Type::typed_ref("unsupported$fndef")
            }

            ty::TyKind::Foreign(..) => {
                vir::Type::typed_ref("unsupported$foreign")
            }

            _ => {
                vir::Type::typed_ref("unsupported")
            }
        };
        Ok(result)
    }

    pub fn encode_invariant_def(self) -> EncodingResult<vir::Function> {
        debug!("[enter] encode_invariant_def({:?})", self.ty);

        // let predicate_name = self.encoder.encode_type_predicate_use(self.ty)?;
        // let self_local_var = vir_local!{ self: {vir::Type::TypedRef(predicate_name.clone())} };

        // let invariant_name = self.encoder.encode_type_invariant_use(self.ty)?;

        // let field_invariants = match self.ty.kind() {
        //     ty::TyKind::Ref(_, ref ty, _) => {
        //         let elem_field = self.encoder.encode_dereference_field(ty)?;
        //         let elem_loc = vir::Expr::from(self_local_var.clone()).field(elem_field);
        //         Some(vec![
        //             self.encoder.encode_invariant_func_app(ty, elem_loc)?
        //         ])
        //     }

        //     ty::TyKind::Adt(ref adt_def, ref subst) if !adt_def.is_box() => {
        //         if self.is_supported_struct_type(adt_def, subst) {
        //             let own_substs =
        //                 ty::List::identity_for_item(self.encoder.env().tcx(), adt_def.did);

        //             // FIXME: this is a hack to support generics. See issue #187.
        //             let mut tymap = HashMap::new();

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

        //             let mut exprs: Vec<vir::Expr> = vec![];
        //             let num_variants = adt_def.variants.len();
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
        //                 //let encoded_args = vec![vir::Expr::from(self_local_var.clone())];
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
        //                         vir::Expr::from(self_local_var.clone()).field(elem_field);
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
        //         let elem_loc = vir::Expr::from(self_local_var.clone()).field(elem_field);
        //         vir::Expr::and(
        //             vir::Expr::acc_permission(elem_loc.clone(), vir::PermAmount::Read),
        //             vir::Expr::pred_permission(elem_loc, vir::PermAmount::Read).unwrap(),
        //         )
        //     }
        //     _ => vir::Expr::predicate_access_predicate(
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
        let typ = self.encoder.encode_type(self.ty)?;
        let self_local_var = vir_local!{ self: {typ} };
        Ok(vir::Function {
            name: self.encoder.encode_type_invariant_use(self.ty)?,
            formal_args: vec![self_local_var],
            return_type: vir::Type::Bool,
            pres: Vec::new(),
            posts: Vec::new(),
            body: Some(true.into()),
        })
    }

    pub fn encode_invariant_use(self) -> EncodingResult<String> {
        debug!("Encode type invariant name '{:?}'", self.ty);
        Ok(format!("{}$inv", self.encode_predicate_use()?))
    }

    pub fn encode_tag_def(self) -> vir::Function {
        debug!("Encode type invariant '{:?}'", self.ty);

        //let pred_name = self.encoder.encode_type_tag_use(self.ty);
        //let self_local_var = vir::LocalVar::new("self", vir::Type::TypedRef(predicate_name.clone()));

        let tag_name = self.encoder.encode_type_tag_use(self.ty);

        let body = match self.ty.kind() {
            ty::TyKind::Param(_param_ty) => None,
            _ => Some((vir::Const::Int((self.ty as *const ty::TyS<'tcx>) as i64)).into()),
        };

        //let precondition = vir::Expr::PredicateAccessPredicate(
        //    predicate_name,
        //    vec![self_local_var.clone().into()],
        //    vir::PermAmount::Write,
        //);

        let function = vir::Function {
            name: tag_name,
            formal_args: Vec::new(),
            return_type: vir::Type::Int,
            pres: Vec::new(),
            posts: Vec::new(),
            body,
        };

        //// Add folding/unfolding
        //foldunfold::add_folding_unfolding_to_function(
        //    function,
        //    self.encoder.get_used_viper_predicates_map()
        //)
        function
    }

    pub fn encode_tag_use(self) -> EncodingResult<String> {
        debug!("Encode type tag name '{:?}'", self.ty);
        Ok(format!("{}$tag", self.encode_predicate_use()?))
    }
}

/// Compute the values that a discriminant can take.
pub fn compute_discriminant_values<'tcx>(adt_def: &'tcx ty::AdtDef, tcx: ty::TyCtxt<'tcx>) -> Vec<i128> {
    let mut discr_values: Vec<i128> = vec![];
    let size = ty::tls::with(|tcx| Integer::from_attr(&tcx, adt_def.repr.discr_type()).size());
    for (_variant_idx, discr) in adt_def.discriminants(tcx) {
        // Sign extend the raw representation to be an i128, to handle *signed* discriminants.
        // See also: https://github.com/rust-lang/rust/blob/b7ebc6b0c1ba3c27ebb17c0b496ece778ef11e18/compiler/rustc_middle/src/ty/util.rs#L35-L45
        discr_values.push(size.sign_extend(discr.val) as i128);
    }
    discr_values
}

/// Encode a disjunction that lists all possible discrimintant values.
pub fn compute_discriminant_bounds<'tcx>(
    adt_def: &'tcx ty::AdtDef,
    tcx: ty::TyCtxt<'tcx>,
    discriminant_loc: &vir::Expr,
) -> vir::Expr {
    /// Try to produce the minimal disjunction.
    fn build_discr_range_expr<T: Ord + PartialEq + Eq + Copy + Into<vir::Expr> + PlusOne>(
        discriminant_loc: &vir::Expr,
        discr_values: Vec<T>,
    ) -> vir::Expr {
        if discr_values.is_empty() {
            // A `false` here is unsound. See issues #38 and #158.
            return true.into();
        }
        range_extract(discr_values)
            .into_iter()
            .map(|(from, to)| {
                if from == to {
                    vir::Expr::eq_cmp(discriminant_loc.clone(), from.into())
                } else {
                    vir::Expr::and(
                        vir::Expr::le_cmp(from.into(), discriminant_loc.clone()),
                        vir::Expr::le_cmp(discriminant_loc.clone(), to.into()),
                    )
                }
            })
            .disjoin()
    }

    // Handle *signed* discriminats
    let discr_values = compute_discriminant_values(adt_def, tcx);
    build_discr_range_expr(discriminant_loc, discr_values)
}

struct HackyExprFolder {
    saelf: vir::LocalVar,
}

impl ExprFolder for HackyExprFolder {
    fn fold_local(&mut self, vir::Local {position, ..}: vir::Local) -> vir::Expr {
        vir::Expr::local_with_pos(self.saelf.clone(), position)
    }
}
