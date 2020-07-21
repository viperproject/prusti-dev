// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::{
    foldunfold,
    spec_encoder::SpecEncoder,
    utils::{range_extract, PlusOne},
    Encoder,
    errors::{ErrorCtxt, PanicCause::Unimplemented},
};
use prusti_common::{
    config, vir,
    vir::{ExprFolder, ExprIterator},
};
use prusti_interface::specifications::*;
use rustc::{
    middle::const_val::ConstVal,
    ty,
    ty::{layout, layout::IntegerExt},
};
use rustc_data_structures::indexed_vec::Idx;
use std::{
    self,
    collections::{hash_map::DefaultHasher, HashMap},
    hash::{Hash, Hasher},
};
use syntax::{ast, attr::SignedInt};

pub struct TypeEncoder<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> {
    encoder: &'p Encoder<'v, 'r, 'a, 'tcx>,
    ty: ty::Ty<'tcx>,
}

impl<'p, 'v, 'r: 'v, 'a: 'r, 'tcx: 'a> TypeEncoder<'p, 'v, 'r, 'a, 'tcx> {
    pub fn new(encoder: &'p Encoder<'v, 'r, 'a, 'tcx>, ty: ty::Ty<'tcx>) -> Self {
        TypeEncoder { encoder, ty }
    }

    /// Is this type supported?
    fn is_supported_type(&self, ty: ty::Ty<'tcx>) -> bool {
        match ty.sty {
            ty::TypeVariants::TyBool
            | ty::TypeVariants::TyInt(_)
            | ty::TypeVariants::TyUint(_)
            | ty::TypeVariants::TyChar
            | ty::TypeVariants::TyRef(_, _, _)
            | ty::TypeVariants::TyAdt(_, _)
            | ty::TypeVariants::TyTuple(_)
            | ty::TypeVariants::TyNever
            | ty::TypeVariants::TyParam(_) => true,
            _ => false,
        }
    }

    fn is_supported_subst(&self, subst: &ty::subst::Substs<'tcx>) -> bool {
        subst.iter().all(|kind| {
            if let ty::subst::UnpackedKind::Type(ty) = kind.unpack() {
                trace!(
                    "is_supported_subst({:?}) = {}",
                    ty,
                    self.is_supported_type(ty)
                );
                self.is_supported_type(ty)
            } else {
                true
            }
        })
    }

    /// Is this type supported?
    fn is_supported_field_type(&self, ty: ty::Ty<'tcx>) -> bool {
        match ty.sty {
            ty::TypeVariants::TyAdt(_, subst) => self.is_supported_subst(subst),
            _ => self.is_supported_type(ty),
        }
    }

    /// Are all fields in the struct of a supported type?
    fn is_supported_struct_type(
        &self,
        adt_def: &ty::AdtDef,
        subst: &ty::subst::Substs<'tcx>,
    ) -> bool {
        let tcx = self.encoder.env().tcx();
        let supported_fields = adt_def.variants.iter().all(|variant| {
            variant.fields.iter().all(|field| {
                let field_ty = field.ty(tcx, subst);
                trace!(
                    "is_supported_type({:?}) = {}",
                    field_ty,
                    self.is_supported_type(field_ty)
                );
                self.is_supported_field_type(field_ty)
            })
        });
        supported_fields && self.is_supported_subst(subst)
    }

    pub fn encode_type(self) -> vir::Type {
        debug!("Encode type '{:?}'", self.ty);
        // will panic if attempting to encode unsupported type
        vir::Type::TypedRef(self.encode_predicate_use().unwrap())
    }

    pub fn encode_value_type(self) -> vir::Type {
        debug!("Encode value type '{:?}'", self.ty);
        match self.ty.sty {
            ty::TypeVariants::TyBool => vir::Type::Bool,

            ty::TypeVariants::TyInt(_) | ty::TypeVariants::TyUint(_) | ty::TypeVariants::TyChar => {
                vir::Type::Int
            }

            ty::TypeVariants::TyRef(_, ref ty, _) => {
                // will panic if attempting to encode unsupported type
                let type_name = self.encoder.encode_type_predicate_use(ty).unwrap();
                vir::Type::TypedRef(type_name)
            }

            ty::TypeVariants::TyAdt(_, _)
            | ty::TypeVariants::TyTuple(_) => {
                let snapshot = self.encoder.encode_snapshot(&self.ty);
                if snapshot.is_defined() {
                    snapshot.get_type()
                } else {
                    unreachable!()
                }
            },

            ty::TypeVariants::TyParam(_) => {
                // will panic if attempting to encode unsupported type
                let type_name = self.encoder.encode_type_predicate_use(self.ty).unwrap();
                vir::Type::TypedRef(type_name)
            }

            ref x => unimplemented!("{:?}", x),
        }
    }

    // TODO CMFIXME: added; remove duplucation
    pub fn encode_ref_value_type(self) -> vir::Type {
        debug!("Encode ref value type '{:?}'", self.ty);
        match self.ty.sty {
            ty::TypeVariants::TyBool => vir::Type::Bool,

            ty::TypeVariants::TyInt(_) | ty::TypeVariants::TyUint(_) | ty::TypeVariants::TyChar => {
                vir::Type::Int
            }

            ty::TypeVariants::TyRef(_, ref ty, _) => {
                let type_name = self.encoder.encode_type_predicate_use(ty).ok().unwrap();
                vir::Type::TypedRef(type_name)
            }

            ty::TypeVariants::TyAdt(_, _)
            | ty::TypeVariants::TyTuple(_) => {
                let snapshot = self.encoder.encode_snapshot(&self.ty);
                if snapshot.is_defined() {
                    let type_name = self.encoder.encode_type_predicate_use(self.ty).ok().unwrap();
                    vir::Type::TypedRef(type_name)
                } else {
                    unreachable!()
                }
            },

            ty::TypeVariants::TyParam(_) => {
                let type_name = self.encoder.encode_type_predicate_use(self.ty).ok().unwrap();
                vir::Type::TypedRef(type_name)
            }

            ref x => unimplemented!("{:?}", x),
        }
    }

    pub fn encode_value_field(self) -> vir::Field {
        trace!("Encode value field for type '{:?}'", self.ty);
        match self.ty.sty {
            ty::TypeVariants::TyBool => vir::Field::new("val_bool", vir::Type::Bool),

            ty::TypeVariants::TyInt(_) | ty::TypeVariants::TyUint(_) | ty::TypeVariants::TyChar => {
                vir::Field::new("val_int", vir::Type::Int)
            }

            ty::TypeVariants::TyRef(_, ref ty, _) => {
                // will panic if attempting to encode unsupported type
                let type_name = self.encoder.encode_type_predicate_use(ty).unwrap();
                vir::Field::new("val_ref", vir::Type::TypedRef(type_name))
            }

            ty::TypeVariants::TyAdt(_, _) // TODO CMFIXME notice that the field is a reference, not a snapshot
            | ty::TypeVariants::TyTuple(_) => {
                let type_name = self.encoder.encode_type_predicate_use(self.ty).ok().unwrap();
                vir::Field::new("val_ref", vir::Type::TypedRef(type_name))
            }

            ty::TypeVariants::TyRawPtr(ty::TypeAndMut { ref ty, .. }) => {
                unimplemented!("Raw pointers are unsupported. (ty={:?})", ty);
            }

            ref x => unimplemented!("{:?}", x),
        }
    }

    fn get_integer_bounds(&self) -> Option<(vir::Expr, vir::Expr)> {
        match self.ty.sty {
            ty::TypeVariants::TyInt(int_ty) => {
                let bounds = match int_ty {
                    ast::IntTy::I8 => (std::i8::MIN.into(), std::i8::MAX.into()),
                    ast::IntTy::I16 => (std::i16::MIN.into(), std::i16::MAX.into()),
                    ast::IntTy::I32 => (std::i32::MIN.into(), std::i32::MAX.into()),
                    ast::IntTy::I64 => (std::i64::MIN.into(), std::i64::MAX.into()),
                    ast::IntTy::I128 => (std::i128::MIN.into(), std::i128::MAX.into()),
                    ast::IntTy::Isize => (std::isize::MIN.into(), std::isize::MAX.into()),
                };
                Some(bounds)
            }
            ty::TypeVariants::TyUint(uint_ty) => {
                let bounds = match uint_ty {
                    ast::UintTy::U8 => (0.into(), std::u8::MAX.into()),
                    ast::UintTy::U16 => (0.into(), std::u16::MAX.into()),
                    ast::UintTy::U32 => (0.into(), std::u32::MAX.into()),
                    ast::UintTy::U64 => (0.into(), std::u64::MAX.into()),
                    ast::UintTy::U128 => (0.into(), std::u128::MAX.into()),
                    ast::UintTy::Usize => (0.into(), std::usize::MAX.into()),
                };
                Some(bounds)
            }
            ty::TypeVariants::TyChar => {
                // char is always four bytes in size
                Some((0.into(), 0xFFFFFFFFu32.into()))
            }
            ty::TypeVariants::TyBool | ty::TypeVariants::TyRef(_, _, _) => None,
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

    pub fn encode_predicate_def(self) -> Vec<vir::Predicate> {
        debug!("Encode type predicate '{:?}'", self.ty);
        // will panic if attempting to encode unsupported type
        let predicate_name = self.encoder.encode_type_predicate_use(self.ty).unwrap();
        let typ = vir::Type::TypedRef(predicate_name.clone());

        match self.ty.sty {
            ty::TypeVariants::TyBool => vec![vir::Predicate::new_primitive_value(
                typ,
                self.encoder.encode_value_field(self.ty),
                None,
                false,
            )],

            ty::TypeVariants::TyInt(_) | ty::TypeVariants::TyUint(_) | ty::TypeVariants::TyChar => {
                let bounds = if config::check_binary_operations() {
                    self.get_integer_bounds()
                } else {
                    None
                };
                let unsigned = if let ty::TypeVariants::TyUint(_) = self.ty.sty {
                    config::encode_unsigned_num_constraint()
                } else {
                    false
                };
                vec![vir::Predicate::new_primitive_value(
                    typ,
                    self.encoder.encode_value_field(self.ty),
                    bounds,
                    unsigned,
                )]
            }

            ty::TypeVariants::TyRawPtr(ty::TypeAndMut { ref ty, .. }) => {
                unimplemented!("Raw pointers are unsupported. (ty={:?})", ty);
            }

            ty::TypeVariants::TyRef(_, ref ty, _) => vec![vir::Predicate::new_struct(
                typ,
                vec![self.encoder.encode_dereference_field(ty)],
            )],

            ty::TypeVariants::TyTuple(elems) => {
                let fields = elems
                    .iter()
                    .enumerate()
                    .map(|(field_num, ty)| {
                        let field_name = format!("tuple_{}", field_num);
                        self.encoder.encode_raw_ref_field(field_name, ty)
                    })
                    .collect();
                vec![vir::Predicate::new_struct(typ, fields)]
            }

            ty::TypeVariants::TyAdt(adt_def, subst) if !adt_def.is_box() => {
                if !self.is_supported_struct_type(adt_def, subst) {
                    vec![vir::Predicate::new_abstract(typ)]
                } else {
                    let num_variants = adt_def.variants.len();
                    let tcx = self.encoder.env().tcx();
                    if num_variants == 1 {
                        debug!("ADT {:?} has only one variant", adt_def);
                        let fields = adt_def.variants[0]
                            .fields
                            .iter()
                            .map(|field| {
                                let field_name = field.ident.to_string();
                                let field_ty = field.ty(tcx, subst);
                                self.encoder.encode_struct_field(&field_name, field_ty)
                            })
                            .collect();
                        vec![vir::Predicate::new_struct(typ, fields)]
                    } else {
                        debug!("ADT {:?} has {} variants", adt_def, num_variants);
                        let discriminant_field = self.encoder.encode_discriminant_field();
                        let this = vir::Predicate::construct_this(typ.clone());
                        let discriminant_loc =
                            vir::Expr::from(this.clone()).field(discriminant_field);
                        let discriminant_bounds =
                            compute_discriminant_bounds(adt_def, tcx, &discriminant_loc);

                        let discriminant_values = compute_discriminant_values(adt_def, tcx);
                        let variants: Vec<_> = adt_def
                            .variants
                            .iter()
                            .zip(discriminant_values)
                            .map(|(variant_def, variant_index)| {
                                let fields = variant_def
                                    .fields
                                    .iter()
                                    .map(|field| {
                                        debug!("Encoding field {:?}", field);
                                        let field_name = &field.ident.as_str();
                                        let field_ty = field.ty(tcx, subst);
                                        self.encoder.encode_struct_field(field_name, field_ty)
                                    })
                                    .collect();
                                let variant_name = &variant_def.name.as_str();
                                let guard = vir::Expr::eq_cmp(
                                    discriminant_loc.clone().into(),
                                    variant_index.into(),
                                );
                                let variant_typ = typ.clone().variant(variant_name);
                                (
                                    guard,
                                    variant_name.to_string(),
                                    vir::StructPredicate::new(variant_typ, fields),
                                )
                            })
                            .collect();
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
                            discriminant_loc,
                            discriminant_bounds,
                            variants,
                        );
                        predicates.push(enum_predicate);
                        predicates
                    }
                }
            }

            ty::TypeVariants::TyAdt(ref adt_def, ref _subst) if adt_def.is_box() => {
                let num_variants = adt_def.variants.len();
                assert_eq!(num_variants, 1);
                let field_ty = self.ty.boxed_ty();
                vec![vir::Predicate::new_struct(
                    typ,
                    vec![self.encoder.encode_dereference_field(field_ty)],
                )]
            }

            ty::TypeVariants::TyNever => {
                // FIXME: This should be a predicate with the body `false`. See issue #38.
                vec![vir::Predicate::new_abstract(typ)]
            }

            ty::TypeVariants::TyParam(_) => {
                // special case: type parameters shall be encoded as *abstract* predicates
                vec![vir::Predicate::new_abstract(typ)]
            }

            ref ty_variant => {
                debug!("Encoding of type '{}' is incomplete", ty_variant);
                vec![vir::Predicate::new_abstract(typ)]
            }
        }
    }

    pub fn encode_predicate_use(self) -> Result<String, ErrorCtxt> {
        debug!("Encode type predicate name '{:?}'", self.ty);

        Ok(match self.ty.sty {
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

            ty::TypeVariants::TyRawPtr(ty::TypeAndMut { ref ty, .. })
            | ty::TypeVariants::TyRef(_, ref ty, _) => {
                format!("ref${}", self.encoder.encode_type_predicate_use(ty)?)
            }

            ty::TypeVariants::TyAdt(adt_def, subst) => {
                let mut composed_name = vec![self.encoder.encode_item_name(adt_def.did)];
                composed_name.push("_beg_".to_string()); // makes generics "less fragile"
                let mut first = true;
                for kind in subst.iter() {
                    if first {
                        first = false
                    } else {
                        // makes generics "less fragile"
                        composed_name.push("_sep_".to_string());
                    }
                    if let ty::subst::UnpackedKind::Type(ty) = kind.unpack() {
                        composed_name.push(self.encoder.encode_type_predicate_use(ty)?)
                    }
                }
                composed_name.push("_end_".to_string()); // makes generics "less fragile"
                composed_name.join("$")
            }

            ty::TypeVariants::TyTuple(elems) => {
                let elem_predicate_names: Result<Vec<String>, ErrorCtxt> = elems
                    .iter()
                    .map(|ty| match self.encoder.encode_type_predicate_use(ty) {
                        Ok(result) => Ok(result),
                        Err(error) => return Err(error),
                    })
                    .collect();
                format!("tuple{}${}", elems.len(), elem_predicate_names?.join("$"))
            }

            ty::TypeVariants::TyNever => "never".to_string(),

            ty::TypeVariants::TyStr => "str".to_string(),

            ty::TypeVariants::TyArray(elem_ty, size) => {
                let scalar_size = match size.val {
                    ConstVal::Value(ref value) => value.to_scalar().unwrap(),
                    x => unimplemented!("{:?}", x),
                };
                format!(
                    "array${}${}",
                    self.encoder.encode_type_predicate_use(elem_ty)?,
                    scalar_size
                        .to_bits(ty::layout::Size::from_bits(64))
                        .ok()
                        .unwrap()
                )
            }

            ty::TypeVariants::TySlice(array_ty) => {
                format!("slice${}", self.encoder.encode_type_predicate_use(array_ty)?)
            }

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
            }

            ty::TypeVariants::TyParam(param_ty) => {
                format!("__TYPARAM__${}$__", param_ty.name.as_str())
            }

            ref x => {
                debug!("Unimplemented! {:?}", x);
                return Err(ErrorCtxt::Panic(Unimplemented));
            }
        })
    }

    pub fn encode_invariant_def(self) -> vir::Function {
        debug!("[enter] encode_invariant_def({:?})", self.ty);

        // will panic if attempting to encode unsupported type
        let predicate_name = self.encoder.encode_type_predicate_use(self.ty).unwrap();
        let self_local_var =
            vir::LocalVar::new("self", vir::Type::TypedRef(predicate_name.clone()));

        let invariant_name = self.encoder.encode_type_invariant_use(self.ty);

        let field_invariants = match self.ty.sty {
            ty::TypeVariants::TyRawPtr(ty::TypeAndMut { ref ty, .. })
            | ty::TypeVariants::TyRef(_, ref ty, _) => {
                let elem_field = self.encoder.encode_dereference_field(ty);
                let elem_loc = vir::Expr::from(self_local_var.clone()).field(elem_field);
                Some(vec![self.encoder.encode_invariant_func_app(ty, elem_loc)])
            }

            ty::TypeVariants::TyAdt(ref adt_def, ref subst) if !adt_def.is_box() => {
                if self.is_supported_struct_type(adt_def, subst) {
                    let own_substs =
                        ty::subst::Substs::identity_for_item(self.encoder.env().tcx(), adt_def.did);

                    {
                        // FIXME; hideous monstrosity...
                        let mut tymap_stack = self.encoder.typaram_repl.borrow_mut();
                        let mut tymap = HashMap::new();

                        for (kind1, kind2) in own_substs.iter().zip(*subst) {
                            if let (
                                ty::subst::UnpackedKind::Type(ty1),
                                ty::subst::UnpackedKind::Type(ty2),
                            ) = (kind1.unpack(), kind2.unpack())
                            {
                                tymap.insert(ty1, ty2);
                            }
                        }
                        tymap_stack.push(tymap);
                    }

                    let mut exprs: Vec<vir::Expr> = vec![];
                    let num_variants = adt_def.variants.len();
                    let tcx = self.encoder.env().tcx();

                    let mut specs: Vec<&TypedSpecificationSet> = Vec::new();
                    if let Some(spec) = self.encoder.get_spec_by_def_id(adt_def.did) {
                        specs.push(spec);
                    }

                    let traits = self.encoder.env().get_traits_decls_for_type(&self.ty);
                    for trait_id in traits {
                        if let Some(spec) = self.encoder.get_spec_by_def_id(trait_id) {
                            specs.push(spec);
                        }
                    }

                    for spec in specs.into_iter() {
                        //let encoded_args = vec![vir::Expr::from(self_local_var.clone())];
                        let encoded_args = vec![];
                        let spec_encoder = SpecEncoder::new_simple(self.encoder, &encoded_args);

                        let mut hacky_folder = HackyExprFolder {
                            saelf: self_local_var.clone(),
                        };

                        match spec {
                            SpecificationSet::Struct(items) => {
                                for item in items {
                                    let enc = spec_encoder.encode_assertion(&item.assertion);
                                    // OPEN TODO: hacky fix here to convert the closure var to "self"...
                                    let enc = hacky_folder.fold(enc);
                                    exprs.push(enc);
                                }
                            }
                            _ => unreachable!(),
                        }
                    }

                    // FIXME; hideous monstrosity...
                    {
                        let mut tymap_stack = self.encoder.typaram_repl.borrow_mut();
                        tymap_stack.pop();
                    }

                    if num_variants == 0 {
                        debug!("ADT {:?} has no variant", adt_def);
                    // `false` here is currently unsound. See issue #158
                    //exprs.push(false.into()); // TODO: See issue #146
                    } else if num_variants == 1 {
                        debug!("ADT {:?} has only one variant", adt_def);

                        for field in &adt_def.variants[0].fields {
                            debug!("Encoding field {:?}", field);
                            let field_name = &field.ident.as_str();
                            let field_ty = field.ty(tcx, subst);
                            let elem_field = self.encoder.encode_struct_field(field_name, field_ty);
                            let elem_loc =
                                vir::Expr::from(self_local_var.clone()).field(elem_field);
                            exprs.push(self.encoder.encode_invariant_func_app(field_ty, elem_loc));
                        }
                    } else {
                        debug!("ADT {:?} has {} variants", adt_def, num_variants);
                        // TODO: https://gitlab.inf.ethz.ch/OU-PMUELLER/prusti-dev/issues/201
                    }

                    Some(exprs)
                } else {
                    // TODO: https://gitlab.inf.ethz.ch/OU-PMUELLER/prusti-dev/issues/201
                    Some(vec![])
                }
            }

            // TODO
            _ => Some(vec![]),
        };

        let precondition = match self.ty.sty {
            ty::TypeVariants::TyRawPtr(ty::TypeAndMut { ref ty, .. })
            | ty::TypeVariants::TyRef(_, ref ty, _) => {
                // This is a reference, so we need to have it already unfolded.
                let elem_field = self.encoder.encode_dereference_field(ty);
                let elem_loc = vir::Expr::from(self_local_var.clone()).field(elem_field);
                vir::Expr::and(
                    vir::Expr::acc_permission(elem_loc.clone(), vir::PermAmount::Read),
                    vir::Expr::pred_permission(elem_loc, vir::PermAmount::Read).unwrap(),
                )
            }
            _ => vir::Expr::predicate_access_predicate(
                predicate_name,
                self_local_var.clone().into(),
                vir::PermAmount::Read,
            ),
        };

        let function = vir::Function {
            name: invariant_name,
            formal_args: vec![self_local_var],
            return_type: vir::Type::Bool,
            pres: vec![precondition],
            posts: Vec::new(),
            body: field_invariants.map(|invs| invs.into_iter().conjoin()),
        };

        // Add folding/unfolding
        let final_function = foldunfold::add_folding_unfolding_to_function(
            function,
            self.encoder.get_used_viper_predicates_map(),
        )
        .ok()
        .unwrap(); // TODO: generate a stub function in case of error
        debug!(
            "[exit] encode_invariant_def({:?}):\n{}",
            self.ty, final_function
        );
        final_function
    }

    pub fn encode_invariant_use(self) -> String {
        debug!("Encode type invariant name '{:?}'", self.ty);
        // will panic if attempting to encode unsupported type
        format!("{}$inv", self.encode_predicate_use().unwrap())
    }

    pub fn encode_tag_def(self) -> vir::Function {
        debug!("Encode type invariant '{:?}'", self.ty);

        //let pred_name = self.encoder.encode_type_tag_use(self.ty);
        //let self_local_var = vir::LocalVar::new("self", vir::Type::TypedRef(predicate_name.clone()));

        let tag_name = self.encoder.encode_type_tag_use(self.ty);

        let body = match self.ty.sty {
            ty::TypeVariants::TyParam(_param_ty) => None,
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

    pub fn encode_tag_use(self) -> String {
        debug!("Encode type tag name '{:?}'", self.ty);
        format!("{}$tag", self.encode_predicate_use().unwrap()) // will panic if attempting to encode unsupported type
    }
}

/// Compute the values that a discriminant can take.
pub fn compute_discriminant_values(adt_def: &ty::AdtDef, tcx: ty::TyCtxt) -> Vec<i128> {
    let mut discr_values: Vec<i128> = vec![];
    // Handle *signed* discriminats
    if let SignedInt(ity) = adt_def.repr.discr_type() {
        let bit_size = layout::Integer::from_attr(tcx, SignedInt(ity))
            .size()
            .bits();
        let shift = 128 - bit_size;
        for (variant_index, _) in adt_def.variants.iter().enumerate() {
            let unsigned_discr = adt_def.discriminant_for_variant(tcx, variant_index).val;
            let casted_discr = unsigned_discr as i128;
            // sign extend the raw representation to be an i128
            let signed_discr = (casted_discr << shift) >> shift;
            discr_values.push(signed_discr);
        }
    } else {
        for (variant_index, _) in adt_def.variants.iter().enumerate() {
            let value = adt_def.discriminant_for_variant(tcx, variant_index).val;
            discr_values.push(value as i128);
        }
    }
    discr_values
}

/// Encode a disjunction that lists all possible discrimintant values.
pub fn compute_discriminant_bounds(
    adt_def: &ty::AdtDef,
    tcx: ty::TyCtxt,
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
                    vir::Expr::eq_cmp(discriminant_loc.clone().into(), from.into())
                } else {
                    vir::Expr::and(
                        vir::Expr::le_cmp(from.into(), discriminant_loc.clone().into()),
                        vir::Expr::le_cmp(discriminant_loc.clone().into(), to.into()),
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
    fn fold_local(&mut self, _var: vir::LocalVar, pos: vir::Position) -> vir::Expr {
        vir::Expr::Local(self.saelf.clone(), pos)
    }
}
