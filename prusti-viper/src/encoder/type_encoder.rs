// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::Encoder;
use encoder::vir;
use encoder::vir::ExprIterator;
use encoder::vir::{Zero, One};
use encoder::utils::range_extract;
use rustc::middle::const_val::ConstVal;
use rustc::ty;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use rustc_data_structures::indexed_vec::Idx;
use syntax::ast;
use std;
use prusti_interface::config;

pub struct TypeEncoder<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> {
    encoder: &'p Encoder<'v, 'r, 'a, 'tcx>,
    ty: ty::Ty<'tcx>
}

impl<'p, 'v, 'r: 'v, 'a: 'r, 'tcx: 'a> TypeEncoder<'p, 'v, 'r, 'a, 'tcx> {
    pub fn new(encoder: &'p Encoder<'v, 'r, 'a, 'tcx>, ty: ty::Ty<'tcx>) -> Self {
        TypeEncoder {
            encoder,
            ty
        }
    }

    pub fn encode_type(self) -> vir::Type {
        debug!("Encode type '{:?}'", self.ty);
        vir::Type::TypedRef(self.encode_predicate_use())
    }

    pub fn encode_value_type(self) -> vir::Type {
        debug!("Encode value type '{:?}'", self.ty);
        match self.ty.sty {
            ty::TypeVariants::TyBool => vir::Type::Bool,

            ty::TypeVariants::TyInt(_) |
            ty::TypeVariants::TyUint(_) |
            ty::TypeVariants::TyChar => vir::Type::Int,

            ty::TypeVariants::TyRawPtr(ty::TypeAndMut { ref ty, .. }) |
            ty::TypeVariants::TyRef(_, ref ty, _) => {
                let type_name = self.encoder.encode_type_predicate_use(ty);
                vir::Type::TypedRef(type_name)
            },

            ty::TypeVariants::TyAdt(_, _) |
            ty::TypeVariants::TyTuple(_) => unimplemented!(),

            ref x => unimplemented!("{:?}", x),
        }
    }

    pub fn encode_value_field(self) -> vir::Field {
        trace!("Encode value field for type '{:?}'", self.ty);
        match self.ty.sty {
            ty::TypeVariants::TyBool => vir::Field::new("val_bool", vir::Type::Bool),

            ty::TypeVariants::TyInt(_) |
            ty::TypeVariants::TyUint(_) |
            ty::TypeVariants::TyChar => vir::Field::new("val_int", vir::Type::Int),

            ty::TypeVariants::TyRawPtr(ty::TypeAndMut { ref ty, .. }) |
            ty::TypeVariants::TyRef(_, ref ty, _) => {
                let type_name = self.encoder.encode_type_predicate_use(ty);
                vir::Field::new("val_ref", vir::Type::TypedRef(type_name))
            },

            ty::TypeVariants::TyAdt(_, _) |
            ty::TypeVariants::TyTuple(_) => unimplemented!(),

            ref x => unimplemented!("{:?}", x),
        }
    }

    fn get_integer_bounds(&self) -> Option<(vir::Expr, vir::Expr)> {
        match self.ty.sty {
            ty::TypeVariants::TyInt(int_ty) => {
                let bounds = match int_ty {
                    ast::IntTy::I8    => (std::i8::MIN.into(),    std::i8::MAX.into(),   ),
                    ast::IntTy::I16   => (std::i16::MIN.into(),   std::i16::MAX.into(),  ),
                    ast::IntTy::I32   => (std::i32::MIN.into(),   std::i32::MAX.into(),  ),
                    ast::IntTy::I64   => (std::i64::MIN.into(),   std::i64::MAX.into(),  ),
                    ast::IntTy::I128  => (std::i128::MIN.into(),  std::i128::MAX.into(), ),
                    ast::IntTy::Isize => (std::isize::MIN.into(), std::isize::MAX.into(),),
                };
                Some(bounds)
            },
            ty::TypeVariants::TyUint(uint_ty) => {
                let bounds = match uint_ty {
                    ast::UintTy::U8    => (0.into(), std::u8::MAX.into(),   ),
                    ast::UintTy::U16   => (0.into(), std::u16::MAX.into(),  ),
                    ast::UintTy::U32   => (0.into(), std::u32::MAX.into(),  ),
                    ast::UintTy::U64   => (0.into(), std::u64::MAX.into(),  ),
                    ast::UintTy::U128  => (0.into(), std::u128::MAX.into(), ),
                    ast::UintTy::Usize => (0.into(), std::usize::MAX.into(),),
                };
                Some(bounds)
            },
            ty::TypeVariants::TyBool |
            ty::TypeVariants::TyChar |
            ty::TypeVariants::TyRef(_, _, _) => None,
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

    pub fn encode_predicate_def(self) -> vir::Predicate {
        debug!("Encode type predicate '{:?}'", self.ty);
        let predicate_name = self.encoder.encode_type_predicate_use(self.ty);
        let self_local_var = vir::LocalVar::new("self", vir::Type::TypedRef(predicate_name.clone()));

        let field_predicates = match self.ty.sty {
            ty::TypeVariants::TyBool => vec![
                vir::Expr::acc_permission(
                    vir::Expr::from(self_local_var.clone()).field(
                        self.encoder.encode_value_field(self.ty)
                    ).into(),
                    vir::Frac::one()
                )
            ],

            ty::TypeVariants::TyInt(int_ty) => {
                let val_field: vir::Expr = vir::Expr::from(self_local_var.clone()).field(
                    self.encoder.encode_value_field(self.ty)
                ).into();

                let mut body = vec![
                    vir::Expr::acc_permission(
                        val_field.clone(),
                        vir::Frac::one()
                    )
                ];

                if config::check_binary_operations() {
                    let (lower, upper) = self.get_integer_bounds().unwrap();
                    body.push(vir::Expr::le_cmp(lower, val_field.clone()));
                    body.push(vir::Expr::le_cmp(val_field.clone(), upper));
                }

                body
            }

            ty::TypeVariants::TyUint(uint_ty) => {
                let val_field: vir::Expr = vir::Expr::from(self_local_var.clone()).field(
                    self.encoder.encode_value_field(self.ty)
                ).into();

                let mut body = vec![
                    vir::Expr::acc_permission(
                        val_field.clone(),
                        vir::Frac::one()
                    )
                ];

                if config::check_binary_operations() {
                    let (lower, upper) = self.get_integer_bounds().unwrap();
                    body.push(vir::Expr::le_cmp(lower, val_field.clone()));
                    body.push(vir::Expr::le_cmp(val_field.clone(), upper));
                }

                body
            }

            ty::TypeVariants::TyChar => {
                let val_field: vir::Expr = vir::Expr::from(self_local_var.clone()).field(
                    self.encoder.encode_value_field(self.ty)
                ).into();
                vec![
                    vir::Expr::acc_permission(
                        val_field.clone(),
                        vir::Frac::one()
                    ),
                    vir::Expr::le_cmp(
                        0.into(),
                        val_field.clone(),
                    ),
                    vir::Expr::le_cmp(
                        val_field.clone(),
                        // char is always four bytes in size
                        0xFFFFFFFFu32.into(),
                    )
                ]
            }

            ty::TypeVariants::TyRawPtr(ty::TypeAndMut { ref ty, .. }) |
            ty::TypeVariants::TyRef(_, ref ty, _) => {
                let predicate_name = self.encoder.encode_type_predicate_use(ty);
                let elem_field = self.encoder.encode_ref_field("val_ref", ty);
                let elem_loc = vir::Expr::from(self_local_var.clone()).field(elem_field);
                vec![
                    vir::Expr::acc_permission(
                        elem_loc.clone().into(),
                        vir::Frac::one()
                    ),
                    vir::Expr::predicate_access_predicate(
                        predicate_name,
                         elem_loc.into(),
                        vir::Frac::one(),
                    ),
                ]
            }

            ty::TypeVariants::TyTuple(elems) => {
                elems.iter().enumerate().flat_map(|(field_num, ty)| {
                    let field_name = format!("tuple_{}", field_num);
                    let elem_field = self.encoder.encode_ref_field(&field_name, ty);
                    let predicate_name = self.encoder.encode_type_predicate_use(ty);
                    let elem_loc = vir::Expr::from(self_local_var.clone()).field(elem_field);
                    vec![
                        vir::Expr::acc_permission(
                            elem_loc.clone().into(),
                            vir::Frac::one()
                        ),
                        vir::Expr::predicate_access_predicate(
                            predicate_name,
                            elem_loc.into(),
                            vir::Frac::one(),
                        ),
                    ]
                }).collect()
            },

            ty::TypeVariants::TyAdt(ref adt_def, ref subst) if !adt_def.is_box() => {
                let mut perms: Vec<vir::Expr> = vec![];
                let num_variants = adt_def.variants.len();
                let tcx = self.encoder.env().tcx();
                if num_variants == 0 {
                    debug!("ADT {:?} has no variant", adt_def);
                } else if num_variants == 1 {
                    debug!("ADT {:?} has only one variant", adt_def);
                    for field in &adt_def.variants[0].fields {
                        debug!("Encoding field {:?}", field);
                        let field_name = format!("enum_0_{}", field.ident.as_str());
                        let field_ty = field.ty(tcx, subst);
                        let elem_field = self.encoder.encode_ref_field(&field_name, field_ty);
                        let predicate_name = self.encoder.encode_type_predicate_use(field_ty);
                        let elem_loc = vir::Expr::from(self_local_var.clone()).field(elem_field);
                        perms.push(
                            vir::Expr::acc_permission(
                                elem_loc.clone().into(),
                                vir::Frac::one()
                            )
                        );
                        perms.push(
                            vir::Expr::predicate_access_predicate(
                                predicate_name,
                                elem_loc.into(),
                                vir::Frac::one(),
                            )
                        )
                    }
                } else {
                    debug!("ADT {:?} has {} variants", adt_def, num_variants);
                    let discriminant_field = self.encoder.encode_discriminant_field();
                    let discriminan_loc = vir::Expr::from(self_local_var.clone()).field(discriminant_field);
                    // acc(self.discriminant)
                    perms.push(
                        vir::Expr::acc_permission(
                            discriminan_loc.clone().into(),
                            vir::Frac::one()
                        )
                    );
                    // 0 <= self.discriminant <= num_variants - 1
                    let mut discr_values = vec![];
                    for (variant_index, _) in adt_def.variants.iter().enumerate() {
                        discr_values.push(
                            adt_def.discriminant_for_variant(tcx, variant_index).val
                        );
                    }
                    let mut discr_exprs = range_extract(discr_values).into_iter().map(
                        |(from, to)| {
                            if from == to {
                                vir::Expr::eq_cmp(
                                    discriminan_loc.clone().into(),
                                    from.into()
                                )
                            } else {
                                vir::Expr::and(
                                    vir::Expr::le_cmp(
                                        from.into(),
                                        discriminan_loc.clone().into()
                                    ),
                                    vir::Expr::le_cmp(
                                        discriminan_loc.clone().into(),
                                        to.into()
                                    )
                                )
                            }
                        }
                    );
                    perms.push(
                        discr_exprs.disjoin()
                    );
                    for (variant_index, variant_def) in adt_def.variants.iter().enumerate() {
                        debug!("Encoding variant {:?}", variant_def);
                        let mut variant_perms: Vec<vir::Expr> = vec![];
                        for field in &variant_def.fields {
                            debug!("Encoding field {:?}", field);
                            let field_name = format!("enum_{}_{}", variant_index, field.ident.as_str());
                            let field_ty = field.ty(tcx, subst);
                            let elem_field = self.encoder.encode_ref_field(&field_name, field_ty);
                            let predicate_name = self.encoder.encode_type_predicate_use(field_ty);
                            let elem_loc = vir::Expr::from(self_local_var.clone()).field(elem_field);
                            variant_perms.push(
                                vir::Expr::acc_permission(
                                    elem_loc.clone().into(),
                                    vir::Frac::one()
                                )
                            );
                            variant_perms.push(
                                vir::Expr::predicate_access_predicate(
                                    predicate_name,
                                    elem_loc.into(),
                                    vir::Frac::one(),
                                )
                            )
                        }
                        if variant_perms.is_empty() {
                            debug!("Variant {} of '{:?}' is empty", variant_index, self.ty)
                        } else {
                            perms.push(
                                variant_perms.into_iter().conjoin()
                            )
                        }
                    }
                }
                perms
            },

            ty::TypeVariants::TyAdt(ref adt_def, ref subst) if adt_def.is_box() => {
                let mut perms: Vec<vir::Expr> = vec![];
                let num_variants = adt_def.variants.len();
                let tcx = self.encoder.env().tcx();
                assert_eq!(num_variants, 1);
                let field_ty = self.ty.boxed_ty();
                let elem_field = self.encoder.encode_ref_field("val_ref", field_ty);
                let predicate_name = self.encoder.encode_type_predicate_use(field_ty);
                let elem_loc = vir::Expr::from(self_local_var.clone()).field(elem_field);
                perms.push(
                    vir::Expr::acc_permission(
                        elem_loc.clone().into(),
                        vir::Frac::one()
                    )
                );
                perms.push(
                    vir::Expr::predicate_access_predicate(
                        predicate_name,
                        elem_loc.into(),
                        vir::Frac::one(),
                    )
                );
                perms
            },

            ty::TypeVariants::TyNever => {
                vec![
                    // A `false` here is unsound. See issue #38.
                    true.into()
                ]
            },

            ref ty_variant => {
                debug!("Encoding of type '{}' is incomplete", ty_variant);
                vec![
                    true.into()
                ]
            },
        };

        vir::Predicate::new(
            predicate_name,
            vec![ self_local_var ],
            Some(
                field_predicates.into_iter().conjoin()
            )
        )
    }

    pub fn encode_predicate_use(self) -> String {
        debug!("Encode type predicate name '{:?}'", self.ty);

        match self.ty.sty {
            ty::TypeVariants::TyBool => "bool".to_string(),

            ty::TypeVariants::TyInt(ast::IntTy::I8) => "i8".to_string(),
            ty::TypeVariants::TyInt(ast::IntTy::I16) => "i16".to_string(),
            ty::TypeVariants::TyInt(ast::IntTy::I32) => "i32".to_string(),
            ty::TypeVariants::TyInt(ast::IntTy::I64) => "i64".to_string(),
            ty::TypeVariants::TyInt(ast::IntTy::I128) => "i128".to_string(),
            ty::TypeVariants::TyInt(ast::IntTy::Isize) => "isize".to_string(),

            ty::TypeVariants::TyUint(ast::UintTy::U8) => "u8".to_string(),
            ty::TypeVariants::TyUint(ast::UintTy::U16) => "u16".to_string(),
            ty::TypeVariants::TyUint(ast::UintTy::U32) => "u32".to_string(),
            ty::TypeVariants::TyUint(ast::UintTy::U64) => "u64".to_string(),
            ty::TypeVariants::TyUint(ast::UintTy::U128) => "u128".to_string(),
            ty::TypeVariants::TyUint(ast::UintTy::Usize) => "usize".to_string(),

            ty::TypeVariants::TyChar => "char".to_string(),

            ty::TypeVariants::TyRawPtr(ty::TypeAndMut { ref ty, .. }) |
            ty::TypeVariants::TyRef(_, ref ty, _) =>
                format!("ref${}", self.encoder.encode_type_predicate_use(ty)),

            ty::TypeVariants::TyAdt(adt_def, subst) => {
                let mut composed_name = vec![
                    self.encoder.encode_item_name(adt_def.did)
                ];
                for kind in subst.iter() {
                    if let ty::subst::UnpackedKind::Type(ty) = kind.unpack() {
                        composed_name.push(
                            self.encoder.encode_type_predicate_use(ty)
                        )
                    }
                }
                composed_name.join("$")
            },

            ty::TypeVariants::TyTuple(elems) => {
                let elem_predicate_names: Vec<String> = elems.iter().map(
                    |ty| self.encoder.encode_type_predicate_use(ty)
                ).collect();
                format!("tuple{}${}", elems.len(), elem_predicate_names.join("$"))
            }

            ty::TypeVariants::TyNever => "never".to_string(),

            ty::TypeVariants::TyStr => "str".to_string(),

            ty::TypeVariants::TyArray(elem_ty, size) => {
                let scalar_size = match size.val {
                    ConstVal::Value(ref value) => {
                        value.to_scalar().unwrap()
                    },
                    x => unimplemented!("{:?}", x)
                };
                format!(
                    "array${}${}",
                    self.encoder.encode_type_predicate_use(elem_ty),
                    scalar_size.to_bits(ty::layout::Size::from_bits(64)).ok().unwrap()
                )
            },

            ty::TypeVariants::TySlice(array_ty) => {
                format!(
                    "slice${}",
                    self.encoder.encode_type_predicate_use(array_ty)
                )
            },

            ty::TypeVariants::TyClosure(def_id, closure_subst) => {
                let subst_hash = {
                    let mut s = DefaultHasher::new();
                    closure_subst.hash(&mut s);
                    s.finish()
                };

                format!(
                    "closure${:?}_{}_{}${}${}",
                    def_id.krate.index(),
                    def_id.index.address_space().index(),
                    def_id.index.as_array_index(),
                    closure_subst.substs.len(),
                    subst_hash
                )
            },

            ref x => unimplemented!("{:?}", x),
        }
    }
}
