// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_interface::environment::{Procedure, ProcedureLoops};
use rustc::hir;
use rustc::hir::def_id::DefId;
use rustc::hir::intravisit::*;
use rustc::hir::map::Node;
use rustc::middle::const_val::ConstVal;
use rustc::mir;
use rustc::mir::interpret::GlobalId;
use rustc::mir::BinOp;
use rustc::mir::UnOp;
use rustc::ty;
use rustc::ty::subst::Substs;
use std::collections::HashSet;
use std::hint::unreachable_unchecked;
use syntax::ast;
use syntax::codemap::Span;
use validators::unsafety_validator::contains_unsafe;
use validators::Reason;
use validators::SupportStatus;

#[macro_export]
macro_rules! unsupported {
    ($self:expr, $span:expr, $reason: expr) => {
        $self.support().unsupported(Reason::new($reason, $span));
    };
}

#[macro_export]
macro_rules! partially {
    ($self:expr, $span:expr, $reason: expr) => {
        $self.support().partially(Reason::new($reason, $span));
    };
}

#[macro_export]
macro_rules! interesting {
    ($self:expr, $reason:expr) => {
        $self.support().interesting($reason);
    };
}

/// Methods that are common to ProcedureValidator and PureFunctionValidator
pub trait CommonValidator<'a, 'tcx: 'a> {
    fn support(&mut self) -> &mut SupportStatus;

    fn get_support_status(self) -> SupportStatus;

    fn tcx(&self) -> ty::TyCtxt<'a, 'tcx, 'tcx>;

    fn check_hir(&mut self, node: Node) {
        match node {
            Node::NodeExpr(hir::Expr {
                node: hir::Expr_::ExprClosure(..),
                span,
                ..
            }) => {
                unsupported!(self, *span, "is a closure");
            }

            Node::NodeTraitItem(hir::TraitItem {
                node: hir::TraitItemKind::Method(ref method_sig, ..),
                span,
                ..
            })
            | Node::NodeImplItem(hir::ImplItem {
                node: hir::ImplItemKind::Method(ref method_sig, ..),
                span,
                ..
            }) => {
                self.check_fn_header(method_sig.header, *span);
            }

            Node::NodeItem(hir::Item {
                node: hir::Item_::ItemFn(_, header, ref generics, _),
                span,
                ..
            }) => {
                for generic_param in generics.params.iter() {
                    match generic_param.kind {
                        hir::GenericParamKind::Type { .. } => {
                            interesting!(self, "uses function type parameters")
                        }

                        hir::GenericParamKind::Lifetime { .. } => {
                            interesting!(self, "uses function lifetime parameters")
                        }
                    }
                }
                if !generics.where_clause.predicates.is_empty() {
                    unsupported!(self, *span, "has lifetimes constraints");
                }
                self.check_fn_header(*header, *span);
            }

            _ => unreachable!(),
        }
    }

    fn check_fn_header(&mut self, fh: hir::FnHeader, span: Span) {
        match fh.unsafety {
            hir::Unsafety::Unsafe => {
                unsupported!(self, span, "is an unsafe function");
            }

            hir::Unsafety::Normal => {} // OK
        }

        match fh.asyncness {
            hir::IsAsync::Async => {
                unsupported!(self, span, "is an asynchronous function");
            }

            hir::IsAsync::NotAsync => {} // OK
        }
    }

    fn check_ty(&mut self, ty: ty::Ty<'tcx>, span: Span) {
        match ty.sty {
            ty::TypeVariants::TyBool => {} // OK

            ty::TypeVariants::TyChar => {} // OK

            ty::TypeVariants::TyInt(_) => {} // OK

            ty::TypeVariants::TyUint(_) => {} // OK

            ty::TypeVariants::TyFloat(..) => unsupported!(self, span, "uses floating-point types"),

            // Structures, enumerations and unions.
            //
            // Substs here, possibly against intuition, *may* contain `TyParam`s.
            // That is, even after substitution it is possible that there are type
            // variables. This happens when the `TyAdt` corresponds to an ADT
            // definition and not a concrete use of it.
            ty::TypeVariants::TyAdt(adt_def, substs) => {
                self.check_ty_adt(adt_def, substs, span);
                for kind in substs.iter() {
                    match kind.unpack() {
                        ty::subst::UnpackedKind::Lifetime(..) => {
                            partially!(self, span, "uses data structures with lifetime parameters")
                        }

                        ty::subst::UnpackedKind::Type(ty) => self.check_ty(ty, span),
                    }
                }
            }

            ty::TypeVariants::TyForeign(..) => unsupported!(self, span, "uses foreign types"),

            ty::TypeVariants::TyStr => partially!(self, span, "uses `str` types"),

            ty::TypeVariants::TyArray(inner_ty, ..) => {
                self.check_inner_ty(inner_ty, span);
                unsupported!(self, span, "uses `array` types");
            }

            ty::TypeVariants::TySlice(inner_ty, ..) => {
                self.check_inner_ty(inner_ty, span);
                unsupported!(self, span, "uses `slice` types");
            }

            ty::TypeVariants::TyRawPtr(..) => {
                partially!(self, span, "uses raw pointers");
            }

            ty::TypeVariants::TyRef(_, inner_ty, _) => self.check_inner_ty(inner_ty, span),

            ty::TypeVariants::TyFnDef(..) => unsupported!(self, span, "uses function types"),

            ty::TypeVariants::TyFnPtr(..) => {
                unsupported!(self, span, "uses function pointer types")
            }

            ty::TypeVariants::TyDynamic(..) => unsupported!(self, span, "uses dynamic trait types"),

            ty::TypeVariants::TyClosure(..) => unsupported!(self, span, "uses closures"),

            ty::TypeVariants::TyGenerator(..) => unsupported!(self, span, "uses generators"),

            ty::TypeVariants::TyGeneratorWitness(..) => unsupported!(self, span, "uses generators"),

            ty::TypeVariants::TyNever => {} // OK

            ty::TypeVariants::TyTuple(inner_tys) => {
                for inner_ty in inner_tys {
                    self.check_inner_ty(inner_ty, span);
                }
            }

            ty::TypeVariants::TyProjection(..) => unsupported!(self, span, "uses associated types"),

            ty::TypeVariants::TyAnon(..) => unsupported!(self, span, "uses anonymized types"),

            ty::TypeVariants::TyParam(..) => {} // OK

            ty::TypeVariants::TyInfer(..) => unsupported!(self, span, "has uninferred types"),

            ty::TypeVariants::TyError => unsupported!(self, span, "has erroneous inferred types"),
        }
    }

    fn check_inner_ty(&mut self, ty: ty::Ty<'tcx>, span: Span);

    fn check_ty_adt(&mut self, adt_def: &ty::AdtDef, substs: &Substs<'tcx>, span: Span) {
        // Do not use this, because the span is often outside the current crate
        //let span = self.tcx().def_span(adt_def.did);

        if adt_def.is_union() {
            unsupported!(self, span, "uses union types");
        }

        if adt_def.is_box() {
            let boxed_ty = substs.type_at(0);
            self.check_inner_ty(boxed_ty, span);
        } else {
            for field_def in adt_def.all_fields() {
                let field_ty = field_def.ty(self.tcx(), substs);
                self.check_inner_ty(field_ty, span);
            }
        }
    }

    fn check_mir_stmt(&mut self, mir: &mir::Mir<'tcx>, stmt: &mir::Statement<'tcx>) {
        trace!("check_mir_stmt {:?}", stmt);
        let span = stmt.source_info.span;

        match stmt.kind {
            mir::StatementKind::Assign(ref place, ref rvalue) => {
                self.check_place(mir, place, span);
                self.check_rvalue(mir, rvalue, span);
            }

            mir::StatementKind::ReadForMatch(ref place) => self.check_place(mir, place, span),

            mir::StatementKind::SetDiscriminant { ref place, .. } => {
                self.check_place(mir, place, span)
            }

            mir::StatementKind::StorageLive(_) => {} // OK

            mir::StatementKind::StorageDead(_) => {} // OK

            mir::StatementKind::InlineAsm { .. } => {
                unsupported!(self, span, "uses inline Assembly")
            }

            mir::StatementKind::Validate(_, _) => {} // OK

            mir::StatementKind::EndRegion(_) => {} // OK

            mir::StatementKind::UserAssertTy(_, _) => {} // OK

            mir::StatementKind::Nop => {} // OK
        }
    }

    fn check_mir_terminator(&mut self, mir: &mir::Mir<'tcx>, term: &mir::Terminator<'tcx>) {
        trace!("check_mir_terminator {:?}", term);
        let span = term.source_info.span;

        match term.kind {
            mir::TerminatorKind::Goto { .. } => {} // OK

            mir::TerminatorKind::SwitchInt { ref discr, .. } => {
                self.check_operand(mir, discr, span)
            }

            mir::TerminatorKind::Resume => {
                // This should be unreachable
                partially!(self, span, "uses `resume` MIR statements");
            }

            mir::TerminatorKind::Abort => {} // OK

            mir::TerminatorKind::Return => {} // OK

            mir::TerminatorKind::Unreachable => {} // OK

            mir::TerminatorKind::Drop { ref location, .. } => self.check_place(mir, location, span),

            mir::TerminatorKind::DropAndReplace {
                ref location,
                ref value,
                ..
            } => {
                self.check_place(mir, location, span);
                self.check_operand(mir, value, span);
            }

            mir::TerminatorKind::Call {
                ref func,
                ref args,
                ref destination,
                ..
            } => {
                self.check_terminator_call(mir, func, args, destination, span);
            }

            mir::TerminatorKind::Assert { ref cond, .. } => {
                interesting!(self, "uses assertions");
                self.check_operand(mir, cond, span)
            }

            mir::TerminatorKind::Yield { .. } => unsupported!(self, span, "uses `yield`"),

            mir::TerminatorKind::GeneratorDrop { .. } => {
                unsupported!(self, span, "uses `generator drop` MIR statement")
            }

            mir::TerminatorKind::FalseEdges { .. } => {} // OK

            mir::TerminatorKind::FalseUnwind { .. } => {} // OK
        }
    }

    fn check_terminator_call(
        &mut self,
        mir: &mir::Mir<'tcx>,
        func: &mir::Operand<'tcx>,
        args: &Vec<mir::Operand<'tcx>>,
        destination: &Option<(mir::Place<'tcx>, mir::BasicBlock)>,
        span: Span,
    ) {
        if let mir::Operand::Constant(box mir::Constant {
            literal:
                mir::Literal::Value {
                    value:
                        ty::Const {
                            ty:
                                &ty::TyS {
                                    sty: ty::TyFnDef(def_id, ref substs),
                                    ..
                                },
                            ..
                        },
                },
            ..
        }) = func
        {
            let proc_name: &str = &self.tcx().absolute_item_path_str(def_id);
            match proc_name {
                "std::rt::begin_panic" | "std::panicking::begin_panic" => {
                    interesting!(self, "uses panics");
                }

                "<std::boxed::Box<T>>::new" => {
                    for arg in args {
                        self.check_operand(mir, arg, span);
                    }
                    if let Some((ref place, _)) = destination {
                        self.check_place(mir, place, span);
                    }
                }

                _ => {
                    for arg in args {
                        self.check_operand(mir, arg, span);
                    }
                    if let Some((ref place, _)) = destination {
                        self.check_place(mir, place, span);
                    }
                    for kind in substs.iter() {
                        match kind.unpack() {
                            ty::subst::UnpackedKind::Lifetime(..) => {} // OK

                            ty::subst::UnpackedKind::Type(ty) => self.check_ty(ty, span),
                        }
                    }
                }
            }
        } else {
            unsupported!(self, span, "uses non explicit function calls");
        }
    }

    fn get_place_ty(&self, mir: &mir::Mir<'tcx>, place: &mir::Place<'tcx>) -> ty::Ty<'tcx> {
        match place {
            mir::Place::Local(ref local) => mir.local_decls[*local].ty,

            mir::Place::Static(box mir::Static { ty, .. }) => ty,

            mir::Place::Projection(box mir::Projection { ref base, ref elem }) => {
                let base_ty = self.get_place_ty(mir, base);
                mir::tcx::PlaceTy::from_ty(base_ty)
                    .projection_ty(self.tcx(), elem)
                    .to_ty(self.tcx())
            }
        }
    }

    fn get_operand_ty(&self, mir: &mir::Mir<'tcx>, operand: &mir::Operand<'tcx>) -> ty::Ty<'tcx> {
        match operand {
            mir::Operand::Copy(ref place) | mir::Operand::Move(ref place) => {
                self.get_place_ty(mir, place)
            }

            mir::Operand::Constant(box mir::Constant { ty, .. }) => ty,
        }
    }

    fn check_place(&mut self, mir: &mir::Mir<'tcx>, place: &mir::Place<'tcx>, span: Span) {
        match place {
            mir::Place::Local(ref local) => {
                let local_ty = &mir.local_decls[*local].ty;
                self.check_ty(local_ty, span);
            }

            mir::Place::Static(..) => unsupported!(self, span, "uses static variables"),

            mir::Place::Projection(box ref projection) => {
                self.check_projection(mir, projection, span);
            }
        }
    }

    fn check_projection(
        &mut self,
        mir: &mir::Mir<'tcx>,
        projection: &mir::PlaceProjection<'tcx>,
        span: Span,
    ) {
        self.check_place(mir, &projection.base, span);
        match projection.elem {
            mir::ProjectionElem::Deref => {} // OK

            mir::ProjectionElem::Field(_, ty) => self.check_inner_ty(ty, span),

            mir::ProjectionElem::Index(..) => unsupported!(self, span, "uses index operations"),

            mir::ProjectionElem::ConstantIndex { .. } => {
                unsupported!(self, span, "uses indices generated by slice patterns")
            }

            mir::ProjectionElem::Subslice { .. } => {
                unsupported!(self, span, "uses indices generated by slice patterns")
            }

            mir::ProjectionElem::Downcast(adt_def, _) => {
                if adt_def.is_union() {
                    unsupported!(self, span, "uses union types");
                }
            }
        }
    }

    fn check_binary_op(
        &mut self,
        op: &mir::BinOp,
        left_ty: ty::Ty<'tcx>,
        right_ty: ty::Ty<'tcx>,
        span: Span,
    ) {
        match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul => {} // OK
            BinOp::Div => {
                interesting!(self, "uses division");
            }
            BinOp::Rem => {} // OK
            BinOp::BitXor | BinOp::BitAnd | BinOp::BitOr => {
                match (&left_ty.sty, &right_ty.sty) {
                    (ty::TypeVariants::TyBool, ty::TypeVariants::TyBool) => {} // OK
                    _ => unsupported!(self, span, "uses bit operations on non-boolean types"),
                }
            }
            BinOp::Shl | BinOp::Shr => unsupported!(self, span, "uses bit shift operations"),
            BinOp::Eq | BinOp::Lt | BinOp::Le | BinOp::Ne | BinOp::Ge | BinOp::Gt => {} // OK
            BinOp::Offset => unsupported!(self, span, "uses offset operation"),
        }
    }

    fn check_unary_op(&mut self, op: &mir::UnOp, ty: ty::Ty<'tcx>, span: Span) {
        match op {
            UnOp::Neg => {} // OK
            UnOp::Not => {
                match &ty.sty {
                    ty::TypeVariants::TyBool => {} // OK
                    _ => unsupported!(self, span, "uses '!' negation for non-boolean types"),
                }
            }
        }
    }

    fn check_rvalue(&mut self, mir: &mir::Mir<'tcx>, rvalue: &mir::Rvalue<'tcx>, span: Span) {
        match rvalue {
            mir::Rvalue::Use(ref operand) => self.check_operand(mir, operand, span),

            mir::Rvalue::Repeat(..) => unsupported!(self, span, "uses `repeat` operations"),

            mir::Rvalue::Ref(_, _, ref place) => self.check_place(mir, place, span),

            mir::Rvalue::Len(..) => unsupported!(self, span, "uses length operations"),

            mir::Rvalue::Cast(cast_kind, ref op, dst_ty) => {
                self.check_cast(mir, *cast_kind, op, dst_ty, span)
            }

            mir::Rvalue::BinaryOp(ref op, ref left_operand, ref right_operand) => {
                let left_ty = self.get_operand_ty(mir, left_operand);
                let right_ty = self.get_operand_ty(mir, right_operand);
                self.check_binary_op(op, left_ty, right_ty, span);
                self.check_operand(mir, left_operand, span);
                self.check_operand(mir, right_operand, span);
            }

            mir::Rvalue::CheckedBinaryOp(ref op, ref left_operand, ref right_operand) => {
                interesting!(self, "uses checked binary operations");
                let left_ty = self.get_operand_ty(mir, left_operand);
                let right_ty = self.get_operand_ty(mir, right_operand);
                self.check_binary_op(op, left_ty, right_ty, span);
                self.check_operand(mir, left_operand, span);
                self.check_operand(mir, right_operand, span);
            }

            mir::Rvalue::UnaryOp(ref op, ref operand) => {
                let ty = self.get_operand_ty(mir, operand);
                self.check_unary_op(op, ty, span);
                self.check_operand(mir, operand, span)
            }

            mir::Rvalue::NullaryOp(mir::NullOp::Box, ty) => self.check_inner_ty(ty, span),

            mir::Rvalue::NullaryOp(mir::NullOp::SizeOf, _) => {
                unsupported!(self, span, "uses `sizeof` operations")
            }

            mir::Rvalue::Discriminant(ref place) => self.check_place(mir, place, span),

            mir::Rvalue::Aggregate(box ref kind, ref operands) => {
                self.check_aggregate(mir, kind, operands, span)
            }
        }
    }

    fn check_cast(
        &mut self,
        mir: &mir::Mir<'tcx>,
        cast_kind: mir::CastKind,
        op: &mir::Operand<'tcx>,
        dst_ty: ty::Ty<'tcx>,
        span: Span,
    ) {
        let src_ty = self.get_operand_ty(mir, op);

        match (&src_ty.sty, &dst_ty.sty) {
            (ty::TypeVariants::TyInt(ast::IntTy::I8), ty::TypeVariants::TyInt(ast::IntTy::I8))
            | (ty::TypeVariants::TyInt(ast::IntTy::I8), ty::TypeVariants::TyInt(ast::IntTy::I16))
            | (ty::TypeVariants::TyInt(ast::IntTy::I8), ty::TypeVariants::TyInt(ast::IntTy::I32))
            | (ty::TypeVariants::TyInt(ast::IntTy::I8), ty::TypeVariants::TyInt(ast::IntTy::I64))
            | (
                ty::TypeVariants::TyInt(ast::IntTy::I8),
                ty::TypeVariants::TyInt(ast::IntTy::I128),
            )
            | (
                ty::TypeVariants::TyInt(ast::IntTy::I16),
                ty::TypeVariants::TyInt(ast::IntTy::I16),
            )
            | (
                ty::TypeVariants::TyInt(ast::IntTy::I16),
                ty::TypeVariants::TyInt(ast::IntTy::I32),
            )
            | (
                ty::TypeVariants::TyInt(ast::IntTy::I16),
                ty::TypeVariants::TyInt(ast::IntTy::I64),
            )
            | (
                ty::TypeVariants::TyInt(ast::IntTy::I16),
                ty::TypeVariants::TyInt(ast::IntTy::I128),
            )
            | (
                ty::TypeVariants::TyInt(ast::IntTy::I32),
                ty::TypeVariants::TyInt(ast::IntTy::I32),
            )
            | (
                ty::TypeVariants::TyInt(ast::IntTy::I32),
                ty::TypeVariants::TyInt(ast::IntTy::I64),
            )
            | (
                ty::TypeVariants::TyInt(ast::IntTy::I32),
                ty::TypeVariants::TyInt(ast::IntTy::I128),
            )
            | (
                ty::TypeVariants::TyInt(ast::IntTy::I64),
                ty::TypeVariants::TyInt(ast::IntTy::I64),
            )
            | (
                ty::TypeVariants::TyInt(ast::IntTy::I64),
                ty::TypeVariants::TyInt(ast::IntTy::I128),
            )
            | (
                ty::TypeVariants::TyInt(ast::IntTy::I128),
                ty::TypeVariants::TyInt(ast::IntTy::I128),
            )
            | (
                ty::TypeVariants::TyInt(ast::IntTy::Isize),
                ty::TypeVariants::TyInt(ast::IntTy::Isize),
            )
            | (ty::TypeVariants::TyChar, ty::TypeVariants::TyChar)
            | (ty::TypeVariants::TyChar, ty::TypeVariants::TyUint(ast::UintTy::U8))
            | (ty::TypeVariants::TyChar, ty::TypeVariants::TyUint(ast::UintTy::U16))
            | (ty::TypeVariants::TyChar, ty::TypeVariants::TyUint(ast::UintTy::U32))
            | (ty::TypeVariants::TyChar, ty::TypeVariants::TyUint(ast::UintTy::U64))
            | (ty::TypeVariants::TyChar, ty::TypeVariants::TyUint(ast::UintTy::U128))
            | (ty::TypeVariants::TyUint(ast::UintTy::U8), ty::TypeVariants::TyChar)
            | (
                ty::TypeVariants::TyUint(ast::UintTy::U8),
                ty::TypeVariants::TyUint(ast::UintTy::U8),
            )
            | (
                ty::TypeVariants::TyUint(ast::UintTy::U8),
                ty::TypeVariants::TyUint(ast::UintTy::U16),
            )
            | (
                ty::TypeVariants::TyUint(ast::UintTy::U8),
                ty::TypeVariants::TyUint(ast::UintTy::U32),
            )
            | (
                ty::TypeVariants::TyUint(ast::UintTy::U8),
                ty::TypeVariants::TyUint(ast::UintTy::U64),
            )
            | (
                ty::TypeVariants::TyUint(ast::UintTy::U8),
                ty::TypeVariants::TyUint(ast::UintTy::U128),
            )
            | (
                ty::TypeVariants::TyUint(ast::UintTy::U16),
                ty::TypeVariants::TyUint(ast::UintTy::U16),
            )
            | (
                ty::TypeVariants::TyUint(ast::UintTy::U16),
                ty::TypeVariants::TyUint(ast::UintTy::U32),
            )
            | (
                ty::TypeVariants::TyUint(ast::UintTy::U16),
                ty::TypeVariants::TyUint(ast::UintTy::U64),
            )
            | (
                ty::TypeVariants::TyUint(ast::UintTy::U16),
                ty::TypeVariants::TyUint(ast::UintTy::U128),
            )
            | (
                ty::TypeVariants::TyUint(ast::UintTy::U32),
                ty::TypeVariants::TyUint(ast::UintTy::U32),
            )
            | (
                ty::TypeVariants::TyUint(ast::UintTy::U32),
                ty::TypeVariants::TyUint(ast::UintTy::U64),
            )
            | (
                ty::TypeVariants::TyUint(ast::UintTy::U32),
                ty::TypeVariants::TyUint(ast::UintTy::U128),
            )
            | (
                ty::TypeVariants::TyUint(ast::UintTy::U64),
                ty::TypeVariants::TyUint(ast::UintTy::U64),
            )
            | (
                ty::TypeVariants::TyUint(ast::UintTy::U64),
                ty::TypeVariants::TyUint(ast::UintTy::U128),
            )
            | (
                ty::TypeVariants::TyUint(ast::UintTy::U128),
                ty::TypeVariants::TyUint(ast::UintTy::U128),
            )
            | (
                ty::TypeVariants::TyUint(ast::UintTy::Usize),
                ty::TypeVariants::TyUint(ast::UintTy::Usize),
            ) => {} // OK

            _ => unsupported!(self, span, "uses unsupported casts"),
        };
    }

    fn check_operand(&mut self, mir: &mir::Mir<'tcx>, operand: &mir::Operand<'tcx>, span: Span) {
        match operand {
            mir::Operand::Copy(ref place) | mir::Operand::Move(ref place) => {
                self.check_place(mir, place, span)
            }

            mir::Operand::Constant(box mir::Constant {
                ty, ref literal, ..
            }) => {
                self.check_literal(literal, span);
                self.check_ty(ty, span);
            }
        }
    }

    fn check_literal(&mut self, literal: &mir::Literal<'tcx>, span: Span) {
        match literal {
            mir::Literal::Value { value } => {
                match value.val {
                    ConstVal::Value(ref value) => {
                        if value.to_scalar().is_none() {
                            unsupported!(self, span, "uses non-scalar literals");
                        }
                    }
                    ConstVal::Unevaluated(def_id, substs) => {
                        // On crate `078_crossbeam` the `const_eval` call fails with
                        // "can't type-check body of DefId(0/0:18 ~ lock_api[964c]::mutex[0]::RawMutex[0]::INIT[0])"
                        // at "const INIT: Self;"
                        partially!(self, span, "uses unevaluated constant");
                        /*
                        let param_env = self.tcx().param_env(def_id);
                        let cid = GlobalId {
                            instance: ty::Instance::new(def_id, substs),
                            promoted: None
                        };
                        if let Ok(const_value) = self.tcx().const_eval(param_env.and(cid)) {
                            if let ConstVal::Value(ref value) = const_value.val {
                                requires!(self, value.to_scalar().is_some(), "uses non-scalar literals");
                            } else {
                                // This should be unreachable
                                unsupported!(self, "uses erroneous unevaluated literals")
                            }
                        } else {
                            // This should be unreachable
                            unsupported!(self, "uses erroneous unevaluated literals")
                        }
                        */
                    }
                };

                self.check_ty(value.ty, span);

                match value.ty.sty {
                    ty::TypeVariants::TyBool
                    | ty::TypeVariants::TyInt(_)
                    | ty::TypeVariants::TyUint(_)
                    | ty::TypeVariants::TyChar => {} // OK

                    _ => unsupported!(
                        self,
                        span,
                        "uses literals of type non-boolean, non-integer or non-char"
                    ),
                };
            }
            mir::Literal::Promoted { .. } => {
                partially!(self, span, "uses promoted constant literals")
            }
        }
    }

    fn check_aggregate(
        &mut self,
        mir: &mir::Mir<'tcx>,
        kind: &mir::AggregateKind<'tcx>,
        operands: &Vec<mir::Operand<'tcx>>,
        span: Span,
    ) {
        trace!("check_aggregate {:?}, {:?}", kind, operands);

        match kind {
            mir::AggregateKind::Array(..) => {
                unsupported!(self, span, "uses arrays");
            }

            mir::AggregateKind::Tuple => {} // OK

            mir::AggregateKind::Adt(_, _, substs, _) => {
                for kind in substs.iter() {
                    match kind.unpack() {
                        ty::subst::UnpackedKind::Lifetime(..) => {
                            partially!(self, span, "uses data structures with lifetime parameters");
                        }

                        ty::subst::UnpackedKind::Type(ty) => self.check_ty(ty, span),
                    }
                }
            }

            mir::AggregateKind::Closure(..) => unsupported!(self, span, "uses closures"),

            mir::AggregateKind::Generator(..) => unsupported!(self, span, "uses generators"),
        }

        for operand in operands {
            self.check_operand(mir, operand, span);
        }
    }
}
