// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::HashMap;
use rustc_middle::ty;
use prusti_common::vir;
use crate::encoder::Encoder;
use crate::encoder::type_encoder::compute_discriminant_values;

/// Encoder of memory equality functions
pub struct MemoryEqEncoder {
    memory_eq_funcs: HashMap<String, Option<vir::Function>>
}

impl MemoryEqEncoder {
    pub fn new() -> Self {
        MemoryEqEncoder {
            memory_eq_funcs: HashMap::new(),
        }
    }

    pub fn get_encoded_functions(&self) -> Vec<vir::Function> {
        self.memory_eq_funcs.values()
            .cloned()
            .map(|x| x.expect("values in memory_eq_funcs should not be None"))
            .collect()
    }

    pub fn encode_memory_eq_func_app<'tcx>(
        &mut self,
        encoder: &Encoder<'_, 'tcx>,
        first: vir::Expr,
        second: vir::Expr,
        self_ty: ty::Ty<'tcx>,
        position: vir::Position,
    ) -> vir::Expr {
        let typ = first.get_type().clone();
        assert!(&typ == second.get_type());
        let mut name = typ.name();
        name.push_str("$$memory_eq$$");
        if !self.memory_eq_funcs.contains_key(&name) {
            self.encode_memory_eq_func(encoder, name.clone(), self_ty);
        }
        let first_local_var = vir::LocalVar::new("self", typ.clone());
        let second_local_var = vir::LocalVar::new("other", typ);
        vir::Expr::FuncApp(
            name,
            vec![first, second],
            vec![first_local_var, second_local_var],
            vir::Type::Bool,
            position,
        )
    }

    /// Note: We generate functions already with the required unfoldings because some types are
    /// huge and fold unfold is too slow for them.
    fn encode_memory_eq_func<'tcx>(
        &mut self,
        encoder: &Encoder<'_, 'tcx>,
        name: String,
        self_ty: ty::Ty<'tcx>
    ) {
        assert!(!self.memory_eq_funcs.contains_key(&name));
        // Mark that we started encoding this function to avoid infinite recursion.
        self.memory_eq_funcs.insert(name.clone(), None);

        // will panic if attempting to encode unsupported type
        let type_name = encoder.encode_type_predicate_use(self_ty).unwrap();
        let typ = vir::Type::TypedRef(type_name.clone());
        let first_local_var = vir::LocalVar::new("self", typ.clone());
        let second_local_var = vir::LocalVar::new("other", typ);
        let precondition = vec![
            vir::Expr::predicate_access_predicate(
                type_name.clone(),
                first_local_var.clone().into(),
                vir::PermAmount::Read,
            ),
            vir::Expr::predicate_access_predicate(
                type_name,
                second_local_var.clone().into(),
                vir::PermAmount::Read,
            ),
        ];
        let body = self.encode_memory_eq_func_body(
            encoder,
            first_local_var.clone().into(),
            second_local_var.clone().into(),
            self_ty
        );
        let function = vir::Function {
            name: name.clone(),
            formal_args: vec![first_local_var, second_local_var],
            return_type: vir::Type::Bool,
            pres: precondition,
            posts: vec![],
            body: body,
        };
        self.memory_eq_funcs.insert(name, Some(function));
    }

    fn encode_memory_eq_func_body<'tcx>(
        &mut self,
        encoder: &Encoder<'_, 'tcx>,
        first: vir::Expr,
        second: vir::Expr,
        self_ty: ty::Ty<'tcx>
    ) -> Option<vir::Expr> {
        let eq = match self_ty.kind() {
            ty::TyKind::Bool
            | ty::TyKind::Int(_)
            | ty::TyKind::Uint(_)
            | ty::TyKind::Char => {
                let field = encoder.encode_value_field(self_ty);
                let first_field = first.clone().field(field.clone());
                let second_field = second.clone().field(field);
                Some(vir::Expr::eq_cmp(first_field, second_field))
            }
            ty::TyKind::Adt(adt_def, subst) if !adt_def.is_box() => {
                // TODO: If adt_def contains fields of unsupported type,
                // we should return None.
                Some(self.encode_memory_eq_adt(
                    encoder,
                    first.clone(),
                    second.clone(),
                    adt_def,
                    subst
                ))
            }
            ty::TyKind::Tuple(elems) => {
                Some(self.encode_memory_eq_tuple(
                    encoder,
                    first.clone(),
                    second.clone(),
                    elems
                ))
            }
            ty::TyKind::Param(_) => {
                None
            },

            ref x => unimplemented!("{:?}", x),
        };
        eq.map(|body| {
            vir::Expr::wrap_in_unfolding(
                first,
                vir::Expr::wrap_in_unfolding(second, body)
            )
        })
    }

    fn encode_memory_eq_adt<'tcx>(
        &mut self,
        encoder: &Encoder<'_, 'tcx>,
        first: vir::Expr,
        second: vir::Expr,
        adt_def: &ty::AdtDef,
        subst: ty::subst::SubstsRef<'tcx>,
    ) -> vir::Expr {
        let tcx = encoder.env().tcx();
        let num_variants = adt_def.variants.len();
        let mut conjuncts = Vec::new();
        if num_variants == 1 {
            // A struct.
            // TODO this should eventually be replaced by using snapshots?
            // conjuncts.push(self.encode_adt_snap_eq_call(first, second));
            let variant_def = &adt_def.non_enum_variant();
            for field in &variant_def.fields {
                let field_name = &field.ident.as_str();
                let field_ty = field.ty(tcx, subst);
                let elem_field = encoder.encode_struct_field(field_name, field_ty);
                let first_field = first.clone().field(elem_field.clone());
                let second_field = second.clone().field(elem_field);
                let eq = self.encode_memory_eq_func_app(
                    encoder,
                    first_field,
                    second_field,
                    field_ty,
                    vir::Position::default()
                );
                conjuncts.push(eq);
            }
        } else {
            // An enum.
            let discr_field = encoder.encode_discriminant_field();
            let first_discriminant = first.clone().field(discr_field.clone());
            let second_discriminant = second.clone().field(discr_field);
            conjuncts.push(vir::Expr::eq_cmp(first_discriminant.clone(), second_discriminant));
            let discriminant_values = compute_discriminant_values(adt_def, tcx);
            let variants = adt_def.variants
                .iter()
                .zip(discriminant_values)
                .map(|(variant_def, variant_index)| {
                    let guard = vir::Expr::eq_cmp(
                        first_discriminant.clone(),
                        variant_index.into(),
                    );
                    let variant_name = &variant_def.ident.as_str();
                    let first_location = first.clone().variant(variant_name);
                    let second_location = second.clone().variant(variant_name);
                    let eq = self.encode_memory_eq_func_app_variant(
                        encoder,
                        first_location,
                        second_location,
                        variant_def,
                        subst,
                        vir::Position::default()
                    );
                    vir::Expr::implies(guard, eq)
                });
            conjuncts.extend(variants);
        }
        vir::ExprIterator::conjoin(&mut conjuncts.into_iter())
    }

    fn encode_memory_eq_tuple<'tcx>(
        &mut self,
        encoder: &Encoder<'_, 'tcx>,
        first: vir::Expr,
        second: vir::Expr,
        elems: ty::subst::SubstsRef<'tcx>,
    ) -> vir::Expr {
        let mut conjuncts = Vec::new();
        for (field_num, arg) in elems.iter().enumerate() {
            let ty = arg.expect_ty();
            let field_name = format!("tuple_{}", field_num);
            let field = encoder.encode_raw_ref_field(field_name, ty);
            let first_field = first.clone().field(field.clone());
            let second_field = second.clone().field(field);
            let eq = self.encode_memory_eq_func_app(
                encoder,
                second_field,
                first_field,
                ty,
                vir::Position::default()
            );
            conjuncts.push(eq);
        }
        vir::ExprIterator::conjoin(&mut conjuncts.into_iter())
    }

    fn encode_memory_eq_func_app_variant<'tcx>(
        &mut self,
        encoder: &Encoder<'_, 'tcx>,
        first: vir::Expr,
        second: vir::Expr,
        self_variant: &ty::VariantDef,
        subst: ty::subst::SubstsRef<'tcx>,
        position: vir::Position,
    ) -> vir::Expr {
        let typ = first.get_type().clone();
        assert!(&typ == second.get_type());
        let mut name = typ.name();
        name.push_str("$$memory_eq$$");
        if !self.memory_eq_funcs.contains_key(&name) {
            self.encode_memory_eq_func_variant(
                encoder,
                name.clone(),
                typ.clone(),
                self_variant,
                subst
            );
        }
        let first_local_var = vir::LocalVar::new("self", typ.clone());
        let second_local_var = vir::LocalVar::new("other", typ);
        vir::Expr::FuncApp(
            name,
            vec![first, second],
            vec![first_local_var, second_local_var],
            vir::Type::Bool,
            position,
        )
    }

    /// Note: We generate functions already with the required unfoldings because some types are
    /// huge and fold unfold is too slow for them.
    fn encode_memory_eq_func_variant<'tcx>(
        &mut self,
        encoder: &Encoder<'_, 'tcx>,
        name: String,
        typ: vir::Type,
        self_variant: &ty::VariantDef,
        subst: ty::subst::SubstsRef<'tcx>,
    ) {
        assert!(!self.memory_eq_funcs.contains_key(&name));
        // Mark that we started encoding this function to avoid infinite recursion.
        self.memory_eq_funcs.insert(name.clone(), None);
        let tcx = encoder.env().tcx();
        let type_name = typ.name();
        let first_local_var = vir::LocalVar::new("self", typ.clone());
        let second_local_var = vir::LocalVar::new("other", typ);
        let precondition = vec![
            vir::Expr::predicate_access_predicate(
                type_name.clone(),
                first_local_var.clone().into(),
                vir::PermAmount::Read,
            ),
            vir::Expr::predicate_access_predicate(
                type_name,
                second_local_var.clone().into(),
                vir::PermAmount::Read,
            ),
        ];
        let mut conjuncts = self_variant.fields
            .iter()
            .map(|field| {
                let field_name = &field.ident.as_str();
                let field_ty = field.ty(tcx, subst);
                let encoded_field = encoder.encode_struct_field(field_name, field_ty);
                let first_field = vir::Expr::from(first_local_var.clone())
                    .field(encoded_field.clone());
                let second_field = vir::Expr::from(second_local_var.clone())
                    .field(encoded_field.clone());
                self.encode_memory_eq_func_app(
                    encoder,
                    first_field,
                    second_field,
                    field_ty,
                    vir::Position::default()
                )
            });
        let conjunction = vir::ExprIterator::conjoin(&mut conjuncts);
        let unfolded_second = vir::Expr::wrap_in_unfolding(
            second_local_var.clone().into(), conjunction);
        let unfolded_first = vir::Expr::wrap_in_unfolding(
            first_local_var.clone().into(), unfolded_second);
        let body = Some(unfolded_first);
        let function = vir::Function {
            name: name.clone(),
            formal_args: vec![first_local_var, second_local_var],
            return_type: vir::Type::Bool,
            pres: precondition,
            posts: vec![],
            body: body,
        };
        self.memory_eq_funcs.insert(name, Some(function));
    }
}
