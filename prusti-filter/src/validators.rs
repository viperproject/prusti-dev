use syntax::ast::NodeId;
use rustc::hir;
use rustc::mir;
use rustc::hir::intravisit::*;
use syntax::codemap::Span;
use rustc::ty;
use rustc::ty::subst::Substs;

macro_rules! requires {
    ($e:expr) => {
        match $e {
            SupportStatus::Unsupported(reason) => return SupportStatus::Unsupported(reason),
            SupportStatus::Supported => {}
        }
    };

    ($e:expr, $reason:expr) => {
        if !$e {
            return SupportStatus::Unsupported(
                format!($reason)
            );
        }
    };

    ($e:expr, $reason:expr, $($args:expr),*) => {
        if !$e {
            return SupportStatus::Unsupported(
                format!($reason, $($args:expr),*)
            );
        }
    };
}

macro_rules! unsupported {
    ($reason:expr) => {
        return SupportStatus::unsupported(
            format!($reason)
        );
    };

    ($reason:expr, $($args:expr),*) => {
        return SupportStatus::unsupported(
            format!($reason, $($args:expr),*)
        );
    };
}

pub enum SupportStatus {
    Supported,
    Unsupported(String)
}

impl SupportStatus {
    pub fn supported() -> Self {
        SupportStatus::Supported
    }
    pub fn unsupported(reason: String) -> Self {
        SupportStatus::Unsupported(reason)
    }
}

pub struct ProcedureValidator<'a, 'tcx: 'a> {
    tcx: ty::TyCtxt<'a, 'tcx, 'tcx>
}

impl<'a, 'tcx: 'a> ProcedureValidator<'a, 'tcx> {
    pub fn new(tcx: ty::TyCtxt<'a, 'tcx, 'tcx>) -> Self {
        ProcedureValidator {
            tcx
        }
    }

    pub fn is_supported_fn(&self, fk: FnKind<'tcx>, _fd: &hir::FnDecl, _b: hir::BodyId, _s: Span, id: NodeId) -> SupportStatus {
        requires!(self.is_supported_fn_kind(fk));

        let def_id = self.tcx.hir.local_def_id(id);
        let sig = self.tcx.fn_sig(def_id);

        requires!(self.is_supported_fn_sig(sig.skip_binder()));

        let mir = self.tcx.mir_validated(def_id).borrow();
        requires!(self.is_supported_mir(&mir));

        SupportStatus::supported()
    }

    fn is_supported_fn_sig(&self, sig: &ty::FnSig<'tcx>) -> SupportStatus {
        requires!(!sig.variadic, "variadic functions are not supported");

        match sig.unsafety {
            hir::Unsafety::Unsafe => {
                unsupported!("unsafe functions are not supported");
            }

            hir::Unsafety::Normal => {} // OK
        }

        for input_ty in sig.inputs() {
            requires!(self.is_supported_ty(input_ty));
        }

        requires!(self.is_supported_ty(sig.output()));

        SupportStatus::supported()
    }

    fn is_supported_fn_kind(&self, fk: FnKind<'tcx>) -> SupportStatus {
        match fk {
            FnKind::Closure(..) => {
                unsupported!("closures are not supported");
            }

            FnKind::ItemFn(_, ref generics, header, _, _) => {
                for generic_param in generics.params.iter() {
                    match generic_param.kind {
                        hir::GenericParamKind::Type {..} => unsupported!("function type parameters are not supported"),

                        hir::GenericParamKind::Lifetime {..} => {} // OK
                    }
                }
                requires!(generics.where_clause.predicates.is_empty(), "lifetimes constraints are not supported");
                requires!(self.is_supported_fn_header(header));
            }

            FnKind::Method(_, ref method_sig, _, _) => {
                requires!(self.is_supported_fn_header(method_sig.header));
            }
        }

        SupportStatus::supported()
    }

    fn is_supported_fn_header(&self, fh: hir::FnHeader) -> SupportStatus {
        match fh.unsafety {
            hir::Unsafety::Unsafe => {
                unsupported!("unsafe functions are not supported");
            }

            hir::Unsafety::Normal => {} // OK
        }

        match fh.asyncness {
            hir::IsAsync::Async => {
                unsupported!("asynchronous functions are not supported");
            }

            hir::IsAsync::NotAsync => {} // OK
        }

        SupportStatus::supported()
    }

    fn is_supported_ty(&self, ty: ty::Ty<'tcx>) -> SupportStatus {
        match ty.sty {
            ty::TypeVariants::TyBool => {} // OK

            ty::TypeVariants::TyChar => unsupported!("type `char` is not supported"),

            ty::TypeVariants::TyInt(_) => {} // OK

            ty::TypeVariants::TyUint(_) => {} // OK

            ty::TypeVariants::TyFloat(..) => unsupported!("floating-point types are not supported"),

            // Structures, enumerations and unions.
            //
            // Substs here, possibly against intuition, *may* contain `TyParam`s.
            // That is, even after substitution it is possible that there are type
            // variables. This happens when the `TyAdt` corresponds to an ADT
            // definition and not a concrete use of it.
            ty::TypeVariants::TyAdt(adt_def, substs) => requires!(self.is_supported_ty_adt(adt_def, substs)),

            ty::TypeVariants::TyForeign(..) => unsupported!("foreign types are not supported"),

            ty::TypeVariants::TyStr => unsupported!("type `str` is not supported"),

            ty::TypeVariants::TyArray(inner_ty, _) => requires!(self.is_supported_inner_ty(inner_ty)),

            ty::TypeVariants::TySlice(inner_ty) => requires!(self.is_supported_inner_ty(inner_ty)),

            ty::TypeVariants::TyRawPtr(..) => unsupported!("raw pointers are not supported"),

            ty::TypeVariants::TyRef(_, inner_ty, hir::MutMutable) => requires!(self.is_supported_inner_ty(inner_ty)),

            ty::TypeVariants::TyRef(_, _, hir::MutImmutable) => unsupported!("shared references are not supported"),

            ty::TypeVariants::TyFnDef(..) => unsupported!("function types are not supported"),

            ty::TypeVariants::TyFnPtr(..) => unsupported!("function pointer types are not supported"),

            ty::TypeVariants::TyDynamic(..) => unsupported!("trait types are not supported"),

            ty::TypeVariants::TyClosure(..) => unsupported!("closures are not supported"),

            ty::TypeVariants::TyGenerator(..) => unsupported!("generators are not supported"),

            ty::TypeVariants::TyGeneratorWitness(..) => unsupported!("types inside generators are not supported"),

            ty::TypeVariants::TyNever => {}, // OK

            ty::TypeVariants::TyTuple(inner_tys) => {
                for inner_ty in inner_tys {
                    requires!(self.is_supported_inner_ty(inner_ty));
                }
            }

            ty::TypeVariants::TyProjection(..) => unsupported!("associated types are not supported"),

            ty::TypeVariants::TyAnon(..) => unsupported!("anonymized types are not supported"),

            ty::TypeVariants::TyParam(..) => unsupported!("generic type parameters are not supported"),

            ty::TypeVariants::TyInfer(..) => unsupported!("uninferred types are not supported"),

            ty::TypeVariants::TyError => unsupported!("erroneous inferred types are not supported"),
        }

        SupportStatus::supported()
    }


    fn is_supported_ty_adt(&self, adt_def: &ty::AdtDef, substs: &Substs<'tcx>) -> SupportStatus {
        requires!(!adt_def.is_union(), "union types are not supported");

        for field_def in adt_def.all_fields() {
            let field_ty = field_def.ty(self.tcx, substs);
            requires!(self.is_supported_inner_ty(field_ty))
        }

        SupportStatus::supported()
    }

    fn is_supported_inner_ty(&self, ty: ty::Ty<'tcx>) -> SupportStatus {
        requires!(self.is_supported_ty(ty));

        match ty.sty {
            ty::TypeVariants::TyRef(..) => unsupported!("references inside other data structures are not supported"),

            _ => {} // OK
        }

        SupportStatus::supported()
    }

    fn is_supported_mir(&self, mir: &mir::Mir<'tcx>) -> SupportStatus {
        requires!(self.is_supported_ty(mir.return_ty()));
        requires!(mir.yield_ty.is_none(), "`yield` is not suported");
        requires!(mir.upvar_decls.is_empty(), "variables captured in closures are not suported");

        for local_decl in &mir.local_decls {
            requires!(self.is_supported_ty(local_decl.ty));
        }

        for basic_block_data in mir.basic_blocks() {
            for stmt in &basic_block_data.statements {
                requires!(self.is_supported_mir_stmt(stmt));
            }
            requires!(self.is_supported_mir_terminator(basic_block_data.terminator.as_ref().unwrap()));
        }

        SupportStatus::supported()
    }

    fn is_supported_mir_stmt(&self, stmt: &mir::Statement<'tcx>) -> SupportStatus {
        match stmt.kind {
            mir::StatementKind::Assign(ref place, ref rvalue) => {
                requires!(self.is_supported_place(place));
                requires!(self.is_supported_rvalue(rvalue));
            },

            mir::StatementKind::ReadForMatch(_) => {} // OK

            mir::StatementKind::SetDiscriminant { ref place, .. } => requires!(self.is_supported_place(place)),

            mir::StatementKind::StorageLive(_) => {} // OK

            mir::StatementKind::StorageDead(_) => {} // OK

            mir::StatementKind::InlineAsm {..} => unsupported!("inline ASM is not supported"),

            mir::StatementKind::Validate(_, _) => {} // OK

            mir::StatementKind::EndRegion(_) => {} // OK

            mir::StatementKind::UserAssertTy(_, _) => {} // OK

            mir::StatementKind::Nop => {} // OK
        }

        SupportStatus::supported()
    }

    fn is_supported_mir_terminator(&self, term: &mir::Terminator<'tcx>) -> SupportStatus {
        match term.kind {
            mir::TerminatorKind::Goto {..} => {} // OK

            mir::TerminatorKind::SwitchInt { ref discr, .. } => requires!(self.is_supported_operand(discr)),

            mir::TerminatorKind::Resume => unsupported!("`resume` MIR statement is not supported"),

            mir::TerminatorKind::Abort => {} // OK

            mir::TerminatorKind::Return => {} // OK

            mir::TerminatorKind::Unreachable => {} // OK

            mir::TerminatorKind::Drop { ref location, .. } => requires!(self.is_supported_place(location)),

            mir::TerminatorKind::DropAndReplace { ref location, ref value, .. } => {
                requires!(self.is_supported_place(location));
                requires!(self.is_supported_operand(value));
            }

            mir::TerminatorKind::Call { ref func, ref args, ref destination, .. } => {
                requires!(self.is_supported_operand(func));
                for arg in args {
                    requires!(self.is_supported_operand(arg));
                }
                if let Some((ref place, _)) = destination {
                    requires!(self.is_supported_place(place));
                }
            }

            mir::TerminatorKind::Assert { ref cond, .. } => requires!(self.is_supported_operand(cond)),

            mir::TerminatorKind::Yield {..} => unsupported!("`yield` MIR statement is not supported"),

            mir::TerminatorKind::GeneratorDrop {..} => unsupported!("`generator drop` MIR statement is not supported"),

            mir::TerminatorKind::FalseEdges {..} => {} // OK

            mir::TerminatorKind::FalseUnwind {..} => {} // OK
        }

        SupportStatus::supported()
    }

    fn is_supported_place(&self, place: &mir::Place<'tcx>) -> SupportStatus {
        match place {
            mir::Place::Local(_) => {} // OK

            mir::Place::Static(..) => unsupported!("static variables are not supported"),

            mir::Place::Projection(_) => {} // OK
        }

        SupportStatus::supported()
    }

    fn is_supported_rvalue(&self, rvalue: &mir::Rvalue<'tcx>) -> SupportStatus {
        match rvalue {
            mir::Rvalue::Use(ref operand) => requires!(self.is_supported_operand(operand)),

            mir::Rvalue::Repeat(..) => unsupported!("`repeat` operations are not supported"),

            mir::Rvalue::Ref(_, mir::BorrowKind::Shared, _) => unsupported!("shared references are not supported"),

            mir::Rvalue::Ref(_, mir::BorrowKind::Unique, ref place) => requires!(self.is_supported_place(place)),

            mir::Rvalue::Ref(_, mir::BorrowKind::Mut {..}, ref place) => requires!(self.is_supported_place(place)),

            mir::Rvalue::Len(ref place) => requires!(self.is_supported_place(place)),

            mir::Rvalue::Cast(..) => unsupported!("cast operations are not supported"),

            mir::Rvalue::BinaryOp(_, ref left_operand, ref right_operand) => {
                requires!(self.is_supported_operand(left_operand));
                requires!(self.is_supported_operand(right_operand));
            }

            mir::Rvalue::CheckedBinaryOp(_, ref left_operand, ref right_operand) => {
                requires!(self.is_supported_operand(left_operand));
                requires!(self.is_supported_operand(right_operand));
            }

            mir::Rvalue::NullaryOp(mir::NullOp::Box, ty) => requires!(self.is_supported_ty(ty)),

            mir::Rvalue::NullaryOp(mir::NullOp::SizeOf, _) => unsupported!("`sizeof` operations are not supported"),

            mir::Rvalue::UnaryOp(_, ref operand) => requires!(self.is_supported_operand(operand)),

            mir::Rvalue::Discriminant(ref place) => requires!(self.is_supported_place(place)),

            mir::Rvalue::Aggregate(box ref kind, ref operands) => requires!(self.is_supported_aggregate(kind, operands)),
        }

        SupportStatus::supported()
    }

    fn is_supported_operand(&self, operand: &mir::Operand<'tcx>) -> SupportStatus {
        match operand {
            mir::Operand::Copy(ref place) => requires!(self.is_supported_place(place)),

            mir::Operand::Move(ref place) => requires!(self.is_supported_place(place)),

            mir::Operand::Constant(box mir::Constant { ty, .. }) => {
                requires!(self.is_supported_ty(ty));
            }
        }

        SupportStatus::supported()
    }

    fn is_supported_aggregate(&self, kind: &mir::AggregateKind<'tcx>, operands: &Vec<mir::Operand<'tcx>>) -> SupportStatus {
        match kind {
            mir::AggregateKind::Array(ty) => requires!(self.is_supported_ty(ty)),

            mir::AggregateKind::Tuple => {} // OK

            mir::AggregateKind::Adt(_, _, substs, _) => {
                for kind in substs.iter() {
                    match kind.unpack() {
                        ty::subst::UnpackedKind::Lifetime(..) => unsupported!("lifetime parameters are not supported"),

                        ty::subst::UnpackedKind::Type(ty) => requires!(self.is_supported_ty(ty)),
                    }
                }
            }

            mir::AggregateKind::Closure(..) => unsupported!("closures are not supported"),

            mir::AggregateKind::Generator(..) => unsupported!("generators are not supported"),
        }

        for operand in operands {
            requires!(self.is_supported_operand(operand));
        }

        SupportStatus::supported()
    }
}
