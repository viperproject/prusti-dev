// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::Encoder;
use encoder::vir;
use rustc::mir;
use rustc::ty;
use rustc::hir::def_id::DefId;
use prusti_interface::data::ProcedureDefId;
use std::collections::HashMap;
use prusti_interface::environment::Environment;
use rustc_data_structures::indexed_vec::Idx;
use encoder::borrows::ProcedureContract;
use encoder::places;
use encoder::vir::ExprIterator;
use encoder::vir::utils::ExprSubPlaceSubstitutor;
use encoder::places::LocalVariableManager;

pub static PRECONDITION_LABEL: &'static str = "pre";

/// Common code used for `ProcedureEncoder` and `PureFunctionEncoder`
#[derive(Clone)]
pub struct MirEncoder<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> {
    encoder: &'p Encoder<'v, 'r, 'a, 'tcx>,
    mir: &'p mir::Mir<'tcx>,
}

impl<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> MirEncoder<'p, 'v, 'r, 'a, 'tcx> {
    pub fn new(encoder: &'p Encoder<'v, 'r, 'a, 'tcx>, mir: &'p mir::Mir<'tcx>) -> Self {
        debug!("MirEncoder constructor");
        MirEncoder {
            encoder,
            mir,
        }
    }

    pub fn encode_local_var_name(&self, local: mir::Local) -> String {
        format!("{:?}", local)
    }

    pub fn get_local_ty(&self, local: mir::Local) -> ty::Ty<'tcx> {
        self.mir.local_decls[local].ty
    }

    pub fn encode_local(&self, local: mir::Local) -> vir::LocalVar {
        let var_name = self.encode_local_var_name(local);
        let type_name = self.encoder.encode_type_predicate_use(self.get_local_ty(local));
        vir::LocalVar::new(var_name, vir::Type::TypedRef(type_name))
    }

    fn encode_local_var_with_name(&self, name: String) -> vir::LocalVar {
        let (index, decl) = self.mir.local_decls.iter_enumerated().find(|(index, decl)| decl.name.is_some() && decl.name.unwrap().to_string() == name).unwrap();
        let var_name = format!("{:?}", index);
        let type_name = self.encoder.encode_type_predicate_use(decl.ty);
        vir::LocalVar::new(var_name, vir::Type::TypedRef(type_name))
    }

    /// Returns
    /// - `vir::Expr`: the expression of the projection;
    /// - `ty::Ty<'tcx>`: the type of the expression;
    /// - `Option<usize>`: optionally, the variant of the enum.
    pub fn encode_place(&self, place: &mir::Place<'tcx>) -> (vir::Place, ty::Ty<'tcx>, Option<usize>) {
        trace!("Encode place {:?}", place);
        match place {
            &mir::Place::Local(local) => (
                self.encode_local(local).into(),
                self.get_local_ty(local),
                None
            ),

            &mir::Place::Projection(ref place_projection) =>
                self.encode_projection(place_projection),

            x => unimplemented!("{:?}", x),
        }
    }

    /// Returns
    /// - `vir::Place`: the place of the projection;
    /// - `ty::Ty<'tcx>`: the type of the place;
    /// - `Option<usize>`: optionally, the variant of the enum.
    fn encode_projection(&self, place_projection: &mir::PlaceProjection<'tcx>)
                         -> (vir::Place, ty::Ty<'tcx>, Option<usize>) {
        trace!("Encode projection {:?}", place_projection);
        let (encoded_base, base_ty, opt_variant_index) =
            self.encode_place(&place_projection.base);

        trace!("place_projection: {:?}", place_projection);
        trace!("base_ty: {:?}", base_ty);

        match &place_projection.elem {
            &mir::ProjectionElem::Field(ref field, _) => {
                match base_ty.sty {
                    ty::TypeVariants::TyBool |
                    ty::TypeVariants::TyInt(_) |
                    ty::TypeVariants::TyUint(_) |
                    ty::TypeVariants::TyRawPtr(_) |
                    ty::TypeVariants::TyRef(_, _, _) => panic!("Type {:?} has no fields", base_ty),

                    ty::TypeVariants::TyTuple(elems) => {
                        let field_name = format!("tuple_{}", field.index());
                        let field_ty = elems[field.index()];
                        let encoded_field = self.encoder.encode_ref_field(&field_name, field_ty);
                        let encoded_projection = encoded_base.access(encoded_field);
                        (encoded_projection, field_ty, None)
                    }

                    ty::TypeVariants::TyAdt(ref adt_def, ref subst) if !adt_def.is_box() => {
                        debug!("subst {:?}", subst);
                        let num_variants = adt_def.variants.len();
                        // FIXME: why this can be None?
                        let variant_index = opt_variant_index.unwrap_or_else(|| {
                            assert!(num_variants == 1);
                            0
                        });
                        let tcx = self.encoder.env().tcx();
                        assert!(variant_index as u128 == adt_def.discriminant_for_variant(tcx, variant_index).val);
                        let field = &adt_def.variants[variant_index].fields[field.index()];
                        let field_name = format!("enum_{}_{}", variant_index, field.ident.as_str());
                        let field_ty = field.ty(tcx, subst);
                        let encoded_field = self.encoder.encode_ref_field(&field_name, field_ty);
                        let encoded_projection = encoded_base.access(encoded_field);
                        (encoded_projection, field_ty, None)
                    }

                    ty::TypeVariants::TyClosure(def_id, ref closure_subst) => {
                        debug!("closure_subst {:?}", closure_subst);
                        let instantiations = self.encoder.get_closure_instantiations(def_id);
                        assert_eq!(instantiations.len(), 1, "Closures must have exactly one instantiation");
                        let (outer_mir_def_id, ref operands) = instantiations[0];
                        let operand = &operands[field.index()];

                        let tcx = self.encoder.env().tcx();
                        let outer_mir = tcx.mir_validated(outer_mir_def_id).borrow();
                        let outer_mir_encoder = MirEncoder::new(self.encoder, &outer_mir);

                        // XXX: Hack to obtain the variable from the MIR in which the closure is declared.
                        // TODO: remove this hack from mir_encoder
                        let node_id = tcx.hir.as_local_node_id(def_id).unwrap();
                        let mut encoded_projection: vir::Place = tcx.with_freevars(node_id, |freevars| {
                            let freevar = &freevars[field.index()];
                            let var_name = tcx.hir.name(freevar.var_id()).to_string();
                            let encoded_var = outer_mir_encoder.encode_local_var_with_name(var_name.clone());
                            trace!("Field {:?} of closure corresponds to outer variable '{}', encoded as {}", field, var_name, encoded_var);
                            vir::Place::from(encoded_var).addr_of()
                        });
                        // Another hack...
                        let field_ty = closure_subst.upvar_tys(def_id, tcx).nth(field.index()).unwrap();
                        let encoded_field_type = self.encoder.encode_type(field_ty);
                        debug!("Rust closure projection {:?}", place_projection);
                        debug!("encoded_projection: {:?}", encoded_projection);

                        assert_eq!(encoded_projection.get_type(), &encoded_field_type);

                        (encoded_projection, field_ty, None)
                    }

                    ref x => unimplemented!("{:?}", x),
                }
            }

            &mir::ProjectionElem::Deref => {
                match base_ty.sty {
                    ty::TypeVariants::TyRawPtr(ty::TypeAndMut { ty, .. }) |
                    ty::TypeVariants::TyRef(_, ty, _) => {
                        let access = if encoded_base.is_addr_of() {
                            encoded_base.parent().unwrap().clone()
                        } else {
                            match encoded_base {
                                vir::Place::AddrOf(box base_base_place, ty) => base_base_place,
                                _ => {
                                    let ref_field = self.encoder.encode_ref_field("val_ref", ty);
                                    encoded_base.access(ref_field)
                                }
                            }
                        };
                        (access, ty, None)
                    }
                    ty::TypeVariants::TyAdt(ref adt_def, ref subst) if adt_def.is_box() => {
                        let access = if encoded_base.is_addr_of() {
                            encoded_base.parent().unwrap().clone()
                        } else {
                            let field_ty = base_ty.boxed_ty();
                            let ref_field = self.encoder.encode_ref_field("val_ref", field_ty);
                            vir::Place::Field(
                                box encoded_base,
                                ref_field,
                            )
                        };
                        (access, base_ty.boxed_ty(), None)
                    }
                    ref x => unimplemented!("{:?}", x),
                }
            }

            &mir::ProjectionElem::Downcast(ref adt_def, variant_index) => {
                debug!("Downcast projection {:?}, {:?}", adt_def, variant_index);
                (encoded_base, base_ty, Some(variant_index))
            }

            x => unimplemented!("{:?}", x),
        }
    }

    fn eval_place(&self, place: &mir::Place<'tcx>) -> vir::Place {
        let (encoded_place, place_ty, _) = self.encode_place(place);
        let value_field = self.encoder.encode_value_field(place_ty);
        encoded_place.access(value_field)
    }

    /// Returns an `vir::Expr` that corresponds to the value of the operand
    pub fn encode_operand_expr(&self, operand: &mir::Operand<'tcx>) -> vir::Expr {
        trace!("Encode operand expr {:?}", operand);
        match operand {
            &mir::Operand::Constant(box mir::Constant { ty, literal: mir::Literal::Value { value }, .. }) => {
                self.encoder.encode_const_expr(value)
            }
            &mir::Operand::Copy(ref place) |
            &mir::Operand::Move(ref place) => {
                let val_place = self.eval_place(&place);
                val_place.into()
            }
            x => unimplemented!("{:?}", x)
        }
    }

    /// Returns an `vir::Type` that corresponds to the type of the value of the operand
    pub fn encode_operand_expr_type(&self, operand: &mir::Operand<'tcx>) -> vir::Type {
        trace!("Encode operand expr {:?}", operand);
        match operand {
            &mir::Operand::Constant(box mir::Constant { ty, .. }) => {
                self.encoder.encode_value_type(ty)
            }
            &mir::Operand::Copy(ref place) |
            &mir::Operand::Move(ref place) => {
                let val_place = self.eval_place(&place);
                val_place.get_type().clone()
            }
            x => unimplemented!("{:?}", x)
        }
    }

    pub fn encode_bin_op_expr(&self, op: mir::BinOp, left: vir::Expr, right: vir::Expr, ty: ty::Ty<'tcx>) -> vir::Expr {
        let is_bool = ty.sty == ty::TypeVariants::TyBool;
        match op {
            mir::BinOp::Eq => vir::Expr::eq_cmp(left, right),
            mir::BinOp::Ne => vir::Expr::ne_cmp(left, right),
            mir::BinOp::Gt => vir::Expr::gt_cmp(left, right),
            mir::BinOp::Ge => vir::Expr::ge_cmp(left, right),
            mir::BinOp::Lt => vir::Expr::lt_cmp(left, right),
            mir::BinOp::Le => vir::Expr::le_cmp(left, right),
            mir::BinOp::Add => vir::Expr::add(left, right),
            mir::BinOp::Sub => vir::Expr::sub(left, right),
            mir::BinOp::Rem => vir::Expr::rem(left, right),
            mir::BinOp::Div => vir::Expr::div(left, right),
            mir::BinOp::Mul => vir::Expr::mul(left, right),
            mir::BinOp::BitAnd if is_bool => vir::Expr::and(left, right),
            mir::BinOp::BitOr if is_bool => vir::Expr::or(left, right),
            mir::BinOp::BitXor if is_bool => vir::Expr::xor(left, right),
            x => unimplemented!("{:?}", x)
        }
    }

    pub fn encode_unary_op_expr(&self, op: mir::UnOp, expr: vir::Expr) -> vir::Expr {
        match op {
            mir::UnOp::Not => vir::Expr::not(expr),
            mir::UnOp::Neg => vir::Expr::minus(expr),
        }
    }

    pub fn encode_bin_op_check(&self, op: mir::BinOp, _left: vir::Expr, _right: vir::Expr) -> vir::Expr {
        warn!("TODO: encoding of bin op check '{:?}' is incomplete", op);
        // TODO
        false.into()
    }

    pub fn encode_operand_place(&self, operand: &mir::Operand<'tcx>) -> Option<vir::Place> {
        debug!("Encode operand place {:?}", operand);
        match operand {
            &mir::Operand::Move(ref place) |
            &mir::Operand::Copy(ref place) => {
                let (src, _, _) = self.encode_place(place);
                Some(src)
            }

            &mir::Operand::Constant(_) => {
                None
            }
        }
    }

    pub fn encode_place_predicate_permission(&self, place: vir::Place) -> Option<vir::Expr> {
        place.typed_ref_name().map(|predicate_name|
            vir::Expr::PredicateAccessPredicate(
                box vir::Expr::PredicateAccess(
                    predicate_name,
                    vec![place.into()],
                ),
                vir::Perm::full(),
            )
        )
    }

    pub fn encode_old_place(&self, mut place: vir::Place, label: &str) -> vir::Expr {
        debug!("encode_old_place {}, {}", place, label);
        if label == PRECONDITION_LABEL {
            // Replace local vars `_1, ..` with `_old_1, ..` in `encoded_place` (see issue #20)
            for local in self.mir.local_decls.indices() {
                let local_var = self.encode_local(local);
                let old_var_name = format!("_old{}", local_var.name);
                let old_local_var = vir::LocalVar::new(old_var_name, local_var.typ.clone());
                trace!("replace {} --> {}", local_var, old_local_var);
                place = place.replace_prefix(&local_var.into(), old_local_var.into());
            }
        } else {
            warn!("TODO: local variables may be evaluated in the wrong state")
            // See issue #20
        }
        vir::Expr::labelled_old(label, place.into())
    }

    pub fn encode_old_expr(&self, mut expr: vir::Expr, label: &str) -> vir::Expr {
        debug!("encode_old_expr {}, {}", expr, label);
        if label == PRECONDITION_LABEL {
            // Replace local vars `_1, ..` with `_old_1, ..` in `encoded_place` (see issue #20)
            for local in self.mir.local_decls.indices() {
                let local_var = self.encode_local(local);
                let old_var_name = format!("_old{}", local_var.name);
                let old_local_var = vir::LocalVar::new(old_var_name, local_var.typ.clone());
                trace!("replace {} --> {}", local_var, old_local_var);
                expr = ExprSubPlaceSubstitutor::substitute(expr, &local_var.into(), old_local_var.into());
            }
        } else {
            warn!("TODO: local variables may be evaluated in the wrong state")
            // See issue #20
        }
        vir::Expr::labelled_old(label, expr)
    }
}
