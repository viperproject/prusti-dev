// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use viper::{self, Viper, Stmt, Expr, VerificationError, CfgMethod};
use viper::{Domain, Field, Function, Predicate, Method};
use viper::AstFactory;
use rustc::mir;
use rustc::ty;
use prusti_interface::environment::Procedure;
use prusti_interface::data::ProcedureDefId;
use prusti_interface::environment::Environment;
use std::collections::HashMap;
use viper::CfgBlockIndex;
use prusti_interface::environment::BasicBlockIndex;
use rustc::mir::TerminatorKind;
use viper::Successor;
use rustc::middle::const_val::{ConstInt, ConstVal};
use encoder::Encoder;
use encoder::borrows::compute_borrow_infos;
use encoder::utils::*;

pub struct TypeEncoder<'p, 'v: 'p, 'tcx: 'v, P: 'v + Procedure<'tcx>> {
    encoder: &'p Encoder<'v, 'tcx, P>,
    ty: ty::Ty<'tcx>
}

impl<'p, 'v: 'p, 'tcx: 'v, P: 'v + Procedure<'tcx>> TypeEncoder<'p, 'v, 'tcx, P> {
    pub fn new(encoder: &'p Encoder<'v, 'tcx, P>, ty: ty::Ty<'tcx>) -> Self {
        TypeEncoder {
            encoder,
            ty
        }
    }

    /*pub fn encode_type_predicate_def(&self, self_loc: Expr<'v>, self_ty: ty::Ty<'tcx>) -> Predicate<'v> {
        let ast = self.encoder.ast_factory();

        let preds = match self_ty.sty {
            ty::TypeVariants::TyBool |
            ty::TypeVariants::TyInt(_) |
            ty::TypeVariants::TyUint(_) => {
                vec![
                    ast.field_access_predicate(
                        ast.field_access(
                            self_loc,
                            self.encoder.encode_value_field(self_ty)
                        ),
                        ast.full_perm()
                    )
                ]
            }

            ty::TypeVariants::TyRawPtr(ty::TypeAndMut { ref ty, .. }) |
            ty::TypeVariants::TyRef(_, ty::TypeAndMut { ref ty, .. }) => {
                let field_loc = ast.field_access(
                    self_loc,
                    self.encoder.encode_value_field(self_ty)
                );
                let mut perms = self.encode_field_permission(field_loc, ty);
                perms.push(
                    ast.field_access_predicate(
                        ast.field_access(
                            self_loc,
                            self.encoder.encode_value_field(self_ty)
                        ),
                        ast.full_perm()
                    )
                );
                perms
            }

            ty::TypeVariants::TyTuple(elems, _) => {
                elems.iter().enumerate().flat_map(|(field_num, ty)| {
                    let field_name = format!("pos_{}", field_num);
                    let elem_field = self.encoder.encode_type_field(self_ty, &field_name, ty);
                    let predicate_name = self.encoder.encode_type_predicate_use(ty);
                    let elem_loc = ast.field_access(
                        self_loc,
                        elem_field
                    );
                    self.encode_field_permission(elem_loc, ty)
                }).collect()
            },

            ty::TypeVariants::TyAdt(_, _) => unimplemented!(),

            ref x => unimplemented!("{:?}", x),
        };


    }*/

    pub fn encode_field_type(self) -> viper::Type<'v> {
        debug!("Encode field type '{:?}'", self.ty);
        let ast = self.encoder.ast_factory();

        match self.ty.sty {
            ty::TypeVariants::TyBool => ast.bool_type(),

            ty::TypeVariants::TyInt(_) |
            ty::TypeVariants::TyUint(_) => ast.int_type(),

            ty::TypeVariants::TyRawPtr(_) |
            ty::TypeVariants::TyRef(_, _) |
            ty::TypeVariants::TyAdt(_, _) |
            ty::TypeVariants::TyTuple(_, _) => ast.ref_type(),

            ref x => unimplemented!("{:?}", x),
        }
    }

    pub fn encode_value_field(self) -> Field<'v> {
        debug!("Encode value field for type '{:?}'", self.ty);
        let ast = self.encoder.ast_factory();

        let field_name = self.encoder.encode_value_field_name(self.ty);

        match self.ty.sty {
            ty::TypeVariants::TyBool => ast.field("val_bool", ast.bool_type()),

            ty::TypeVariants::TyInt(_) => ast.field("val_int", ast.int_type()),
            ty::TypeVariants::TyUint(_) => ast.field("val_uint", ast.int_type()),

            ty::TypeVariants::TyRawPtr(_) |
            ty::TypeVariants::TyRef(_, _) |
            ty::TypeVariants::TyAdt(_, _) |
            ty::TypeVariants::TyTuple(_, _) => ast.field("val_ref", ast.ref_type()),

            ref x => unimplemented!("{:?}", x),
        }
    }

    pub fn encode_value_field_name(self) -> String {
        debug!("Encode value field name for type '{:?}'", self.ty);
        match self.ty.sty {
            ty::TypeVariants::TyBool => "val_bool",

            ty::TypeVariants::TyInt(_) => "val_int",
            ty::TypeVariants::TyUint(_) => "val_uint",

            ty::TypeVariants::TyRawPtr(_) |
            ty::TypeVariants::TyRef(_, _) => "val_ref",

            ty::TypeVariants::TyAdt(_, _) |
            ty::TypeVariants::TyTuple(_, _) => unimplemented!(),

            ref x => unimplemented!("{:?}", x),
        }.to_string()
    }

    pub fn encode_predicate_def(self) -> Predicate<'v> {
        debug!("Encode type predicate '{:?}'", self.ty);
        let ast = self.encoder.ast_factory();

        let predicate_name = self.encoder.encode_type_predicate_use(self.ty);
        let self_local_var = ast.local_var("self", ast.ref_type());

        let field_predicates = match self.ty.sty {
            ty::TypeVariants::TyBool |
            ty::TypeVariants::TyInt(_) |
            ty::TypeVariants::TyUint(_) =>
                vec![
                    ast.field_access_predicate(
                        ast.field_access(
                            self_local_var,
                            self.encoder.encode_value_field(self.ty)
                        ),
                        ast.full_perm()
                    )
                ],

            ty::TypeVariants::TyRawPtr(ty::TypeAndMut { ref ty, .. }) |
            ty::TypeVariants::TyRef(_, ty::TypeAndMut { ref ty, .. }) => {
                let predicate_name = self.encoder.encode_type_predicate_use(ty);
                let elem_field = self.encoder.encode_ref_field("val_ref");
                let elem_loc = ast.field_access(
                    self_local_var,
                    elem_field
                );
                vec![
                    ast.field_access_predicate(
                        elem_loc,
                        ast.full_perm()
                    ),
                    ast.predicate_access_predicate(
                        ast.predicate_access(
                            &[ elem_loc ],
                            &predicate_name
                        ),
                        ast.full_perm()
                    ),
                ]
            }

            ty::TypeVariants::TyTuple(elems, _) => {
                elems.iter().enumerate().flat_map(|(field_num, ty)| {
                    let field_name = format!("pos_{}", field_num);
                    let elem_field = self.encoder.encode_ref_field(&field_name);
                    let predicate_name = self.encoder.encode_type_predicate_use(ty);
                    let elem_loc = ast.field_access(
                        self_local_var,
                        elem_field
                    );
                    vec![
                        ast.field_access_predicate(
                            elem_loc,
                            ast.full_perm()
                        ),
                        ast.predicate_access_predicate(
                            ast.predicate_access(
                                &[ elem_loc ],
                                &predicate_name
                            ),
                            ast.full_perm()
                        ),
                    ]
                }).collect()
            },

            ty::TypeVariants::TyAdt(_, _) => unimplemented!(),

            ref x => unimplemented!("{:?}", x),
        };

        ast.predicate(
            &predicate_name,
            &[
                ast.local_var_decl("self", ast.ref_type())
            ],
            Some(
                if field_predicates.is_empty() {
                    ast.true_lit()
                } else {
                    field_predicates.iter().skip(1).fold(
                        field_predicates[0],
                        |a, b| ast.and(a, *b)
                    )
                }
            )
        )
    }

    pub fn encode_predicate_use(self) -> String {
        debug!("Encode type predicate name '{:?}'", self.ty);

        match self.ty.sty {
            ty::TypeVariants::TyBool => "bool".to_string(),

            ty::TypeVariants::TyInt(_) => "int".to_string(),
            ty::TypeVariants::TyUint(_) => "uint".to_string(),

            ty::TypeVariants::TyRawPtr(ty::TypeAndMut { ref ty, .. }) |
            ty::TypeVariants::TyRef(_, ty::TypeAndMut { ref ty, .. }) =>
                format!("ref${}", self.encoder.encode_type_predicate_use(ty)),

            ty::TypeVariants::TyAdt(&ty::AdtDef { did, .. }, _) =>
                self.encoder.encode_type_name(did),

            ty::TypeVariants::TyTuple(elems, _) => {
                let elem_predicate_names: Vec<String> = elems.iter().map(
                    |ty| self.encoder.encode_type_predicate_use(ty)
                ).collect();
                format!("tuple{}${}", elems.len(), elem_predicate_names.connect("$"))
            }

            ref x => unimplemented!("{:?}", x),
        }
    }
}
