use syntax::ast::NodeId;
use rustc::hir;
use rustc::mir;
use rustc::hir::intravisit::*;
use syntax::codemap::Span;
use rustc::ty;
use rustc::ty::subst::Substs;
use validators::SupportStatus;
use rustc::hir::def_id::DefId;
use std::collections::HashSet;
use prusti_interface::environment::Procedure;

pub struct PureFunctionValidator<'a, 'tcx: 'a> {
    tcx: ty::TyCtxt<'a, 'tcx, 'tcx>,
    support: SupportStatus,
    visited_inner_type_variants: HashSet<&'tcx ty::TypeVariants<'tcx>>,
    visited_fn: HashSet<DefId>,
}

macro_rules! skip_visited_fn {
    ($self:expr, $def_id:expr) => {
        if $self.visited_fn.contains(&$def_id) {
            return;
        } else {
            $self.visited_fn.insert($def_id);
        }
    };
}

macro_rules! skip_visited_inner_type_variant {
    ($self:expr, $tv:expr) => {
        if $self.visited_inner_type_variants.contains(&$tv) {
            return;
        } else {
            $self.visited_inner_type_variants.insert($tv);
        }
    };
}

impl<'a, 'tcx: 'a> PureFunctionValidator<'a, 'tcx> {
    pub fn new(tcx: ty::TyCtxt<'a, 'tcx, 'tcx>) -> Self {
        PureFunctionValidator {
            tcx,
            support: SupportStatus::new(),
            visited_inner_type_variants: HashSet::new(),
            visited_fn: HashSet::new(),
        }
    }

    pub fn get_support_status(self) -> SupportStatus {
        self.support
    }

    pub fn check_fn(&mut self, fk: FnKind<'tcx>, _fd: &hir::FnDecl, _b: hir::BodyId, _s: Span, id: NodeId) {
        self.check_fn_kind(fk);

        let def_id = self.tcx.hir.local_def_id(id);
        self.check_fn_item(def_id);
    }

    pub fn check_fn_item(&mut self, def_id: DefId) {
        skip_visited_fn!(self, def_id);

        let sig = self.tcx.fn_sig(def_id);

        self.check_fn_sig(sig.skip_binder());

        if self.tcx.hir.as_local_node_id(def_id).is_some() {
            let procedure = Procedure::new(self.tcx, def_id);
            self.check_mir(&procedure);
        } else {
            partially!(self, "function calls to outer crates are partially supported")
        }
    }

    fn check_fn_sig(&mut self, sig: &ty::FnSig<'tcx>) {
        requires!(self, !sig.variadic, "variadic functions are not supported");

        match sig.unsafety {
            hir::Unsafety::Unsafe => {
                unsupported!(self, "unsafe functions are not supported");
            }

            hir::Unsafety::Normal => {} // OK
        }

        for input_ty in sig.inputs() {
            self.check_local_ty(input_ty);
        }

        self.check_return_ty(sig.output());
    }

    fn check_fn_kind(&mut self, fk: FnKind<'tcx>) {
        match fk {
            FnKind::Closure(..) => {
                unsupported!(self, "closures are not supported");
            }

            FnKind::ItemFn(_, ref generics, header, _, _) => {
                for generic_param in generics.params.iter() {
                    match generic_param.kind {
                        hir::GenericParamKind::Type {..} => unsupported!(self, "function type parameters are not supported"),

                        hir::GenericParamKind::Lifetime {..} => {} // OK
                    }
                }
                requires!(self, generics.where_clause.predicates.is_empty(), "lifetimes constraints are not supported");
                self.check_fn_header(header);
            }

            FnKind::Method(_, ref method_sig, _, _) => {
                self.check_fn_header(method_sig.header);
            }
        }
    }

    fn check_fn_header(&mut self, fh: hir::FnHeader) {
        match fh.unsafety {
            hir::Unsafety::Unsafe => {
                unsupported!(self, "unsafe functions are not supported");
            }

            hir::Unsafety::Normal => {} // OK
        }

        match fh.asyncness {
            hir::IsAsync::Async => {
                unsupported!(self, "asynchronous functions are not supported");
            }

            hir::IsAsync::NotAsync => {} // OK
        }
    }

    fn check_return_ty(&mut self, ty: ty::Ty<'tcx>) {
        match ty.sty {
            ty::TypeVariants::TyBool => {} // OK

            ty::TypeVariants::TyInt(_) => {} // OK

            ty::TypeVariants::TyUint(_) => {} // OK

            _ => unsupported!(self, "pure functions can only return integer or boolean values"),
        }

        self.check_local_ty(ty);
    }

    fn check_local_ty(&mut self, ty: ty::Ty<'tcx>) {
        match ty.sty {
            ty::TypeVariants::TyBool => {} // OK

            ty::TypeVariants::TyChar => {} // OK

            ty::TypeVariants::TyInt(_) => {} // OK

            ty::TypeVariants::TyUint(_) => {} // OK

            ty::TypeVariants::TyFloat(..) => unsupported!(self, "floating-point types are not supported"),

            // Structures, enumerations and unions.
            //
            // Substs here, possibly against intuition, *may* contain `TyParam`s.
            // That is, even after substitution it is possible that there are type
            // variables. This happens when the `TyAdt` corresponds to an ADT
            // definition and not a concrete use of it.
            ty::TypeVariants::TyAdt(adt_def, substs) => self.check_ty_adt(adt_def, substs),

            ty::TypeVariants::TyForeign(..) => unsupported!(self, "foreign types are not supported"),

            ty::TypeVariants::TyStr => partially!(self, "`str` types are ignored"),

            ty::TypeVariants::TyArray(inner_ty, ..) => {
                self.check_inner_ty(inner_ty);
                unsupported!(self, "`array` types are not supported")
            },

            ty::TypeVariants::TySlice(inner_ty, ..) => {
                self.check_inner_ty(inner_ty);
                unsupported!(self, "`slice` types are not supported")
            },

            ty::TypeVariants::TyRawPtr(ty::TypeAndMut { ty: inner_ty, .. }) => self.check_inner_ty(inner_ty),

            ty::TypeVariants::TyRef(_, inner_ty, _) => self.check_inner_ty(inner_ty),

            ty::TypeVariants::TyFnDef(..) => unsupported!(self, "function types are not supported"),

            ty::TypeVariants::TyFnPtr(..) => unsupported!(self, "function pointer types are not supported"),

            ty::TypeVariants::TyDynamic(..) => unsupported!(self, "trait types are not supported"),

            ty::TypeVariants::TyClosure(..) => unsupported!(self, "closures are not supported"),

            ty::TypeVariants::TyGenerator(..) => unsupported!(self, "generators are not supported"),

            ty::TypeVariants::TyGeneratorWitness(..) => unsupported!(self, "types inside generators are not supported"),

            ty::TypeVariants::TyNever => {}, // OK

            ty::TypeVariants::TyTuple(inner_tys) => {
                for inner_ty in inner_tys {
                    self.check_inner_ty(inner_ty);
                }
            }

            ty::TypeVariants::TyProjection(..) => unsupported!(self, "associated types are not supported"),

            ty::TypeVariants::TyAnon(..) => unsupported!(self, "anonymized types are not supported"),

            ty::TypeVariants::TyParam(..) => unsupported!(self, "generic type parameters are not supported"),

            ty::TypeVariants::TyInfer(..) => unsupported!(self, "uninferred types are not supported"),

            ty::TypeVariants::TyError => unsupported!(self, "erroneous inferred types are not supported"),
        }
    }


    fn check_ty_adt(&mut self, adt_def: &ty::AdtDef, substs: &Substs<'tcx>) {
        requires!(self, !adt_def.is_union(), "union types are not supported");

        for field_def in adt_def.all_fields() {
            let field_ty = field_def.ty(self.tcx, substs);
            self.check_inner_ty(field_ty)
        }
    }

    fn check_inner_ty(&mut self, ty: ty::Ty<'tcx>) {
        skip_visited_inner_type_variant!(self, &ty.sty);

        self.check_local_ty(ty);

        match ty.sty {
            ty::TypeVariants::TyRef(..) => partially!(self, "references inside data structures are partially supported"),

            _ => {} // OK
        }
    }

    fn check_mir(&mut self, procedure: &Procedure<'a, 'tcx>) {
        let mir = procedure.get_mir();
        self.check_local_ty(mir.return_ty());
        requires!(self, mir.yield_ty.is_none(), "`yield` is not supported");
        requires!(self, mir.upvar_decls.is_empty(), "variables captured in closures are not supported");

        //for local_decl in &mir.local_decls {
        //    self.check_local_ty(local_decl.ty);
        //}

        // TODO: check absence of loops
        // TODO: check only blocks that may lead to a `Return` terminator
        for (index, basic_block_data) in mir.basic_blocks().iter_enumerated() {
            if !procedure.is_reachable_block(index) || procedure.is_spec_block(index) {
                continue;
            }
            for stmt in &basic_block_data.statements {
                self.check_mir_stmt(stmt);
            }
            self.check_mir_terminator(basic_block_data.terminator.as_ref().unwrap());
        }
    }

    fn check_mir_stmt(&mut self, stmt: &mir::Statement<'tcx>) {
        match stmt.kind {
            mir::StatementKind::Assign(ref place, ref rvalue) => {
                self.check_place(place);
                self.check_rvalue(rvalue);
            },

            mir::StatementKind::ReadForMatch(_) => {} // OK

            mir::StatementKind::SetDiscriminant { ref place, .. } => self.check_place(place),

            mir::StatementKind::StorageLive(_) => {} // OK

            mir::StatementKind::StorageDead(_) => {} // OK

            mir::StatementKind::InlineAsm {..} => unsupported!(self, "inline ASM is not supported"),

            mir::StatementKind::Validate(_, _) => {} // OK

            mir::StatementKind::EndRegion(_) => {} // OK

            mir::StatementKind::UserAssertTy(_, _) => {} // OK

            mir::StatementKind::Nop => {} // OK
        }
    }

    fn check_mir_terminator(&mut self, term: &mir::Terminator<'tcx>) {
        match term.kind {
            mir::TerminatorKind::Goto {..} => {} // OK

            mir::TerminatorKind::SwitchInt { ref discr, .. } => self.check_operand(discr),

            mir::TerminatorKind::Resume => {
                unsupported!(self, "reachable `resume` MIR statements are unsupported");
            },

            mir::TerminatorKind::Abort => {} // OK

            mir::TerminatorKind::Return => {} // OK

            mir::TerminatorKind::Unreachable => {} // OK

            mir::TerminatorKind::Drop { ref location, .. } => self.check_place(location),

            mir::TerminatorKind::DropAndReplace { ref location, ref value, .. } => {
                self.check_place(location);
                self.check_operand(value);
            }

            mir::TerminatorKind::Call { ref func, ref args, ref destination, .. } => {
                if let mir::Operand::Constant(
                    box mir::Constant {
                        literal: mir::Literal::Value {
                            value: ty::Const {
                                ty: &ty::TyS {
                                    sty: ty::TyFnDef(def_id, ..),
                                    ..
                                },
                                ..
                            }
                        },
                        ..
                    }
                ) = func {
                    for arg in args {
                        self.check_operand(arg);
                    }
                    if let Some((ref place, _)) = destination {
                        self.check_place(place);
                    }
                    requires!(
                        self, self.tcx.hir.as_local_node_id(def_id).is_some(),
                        "calling functions from an external crate is not supported"
                    );
                } else {
                    unsupported!(self, "non explicit function calls are not supported");
                }
            }

            mir::TerminatorKind::Assert { ref cond, .. } => self.check_operand(cond),

            mir::TerminatorKind::Yield {..} => unsupported!(self, "`yield` MIR statement is not supported"),

            mir::TerminatorKind::GeneratorDrop {..} => unsupported!(self, "`generator drop` MIR statement is not supported"),

            mir::TerminatorKind::FalseEdges {..} => {} // OK

            mir::TerminatorKind::FalseUnwind {..} => {} // OK
        }
    }

    fn check_place(&mut self, place: &mir::Place<'tcx>) {
        match place {
            mir::Place::Local(_) => {} // OK

            mir::Place::Static(..) => unsupported!(self, "static variables are not supported"),

            mir::Place::Projection(box ref projection) => self.check_projection(projection),
        }
    }

    fn check_projection(&mut self, projection: &mir::PlaceProjection<'tcx>) {
        match projection.elem {
            mir::ProjectionElem::Deref => {} // OK

            mir::ProjectionElem::Field(_, ty) => self.check_inner_ty(ty),

            mir::ProjectionElem::Index(..) => unsupported!(self, "index operations are not supported"),

            mir::ProjectionElem::ConstantIndex {..} => unsupported!(self, "indices generated by slice patterns are not supported"),

            mir::ProjectionElem::Subslice {..} => unsupported!(self, "indices generated by slice patterns are not supported"),

            mir::ProjectionElem::Downcast(_, _) => {} // OK
        }
    }

    fn check_rvalue(&mut self, rvalue: &mir::Rvalue<'tcx>) {
        match rvalue {
            mir::Rvalue::Use(ref operand) => self.check_operand(operand),

            mir::Rvalue::Repeat(..) => unsupported!(self, "`repeat` operations are not supported"),

            mir::Rvalue::Ref(_, _, ref place) => self.check_place(place),

            mir::Rvalue::Len(ref place) => self.check_place(place),

            mir::Rvalue::Cast(..) => unsupported!(self, "cast operations are not supported"),

            mir::Rvalue::BinaryOp(_, ref left_operand, ref right_operand) => {
                self.check_operand(left_operand);
                self.check_operand(right_operand);
            }

            mir::Rvalue::CheckedBinaryOp(_, ref left_operand, ref right_operand) => {
                self.check_operand(left_operand);
                self.check_operand(right_operand);
            }

            mir::Rvalue::NullaryOp(mir::NullOp::Box, ty) => self.check_inner_ty(ty),

            mir::Rvalue::NullaryOp(mir::NullOp::SizeOf, _) => unsupported!(self, "`sizeof` operations are not supported"),

            mir::Rvalue::UnaryOp(_, ref operand) => self.check_operand(operand),

            mir::Rvalue::Discriminant(ref place) => self.check_place(place),

            mir::Rvalue::Aggregate(box ref kind, ref operands) => self.check_aggregate(kind, operands),
        }
    }

    fn check_operand(&mut self, operand: &mir::Operand<'tcx>) {
        match operand {
            mir::Operand::Copy(ref place) => {
                self.check_place(place)
            }

            mir::Operand::Move(ref place) => {
                self.check_place(place)
            }

            mir::Operand::Constant(box mir::Constant { ty, .. }) => {
                self.check_local_ty(ty);
            }
        }
    }

    fn check_aggregate(&mut self, kind: &mir::AggregateKind<'tcx>, operands: &Vec<mir::Operand<'tcx>>) {
        match kind {
            mir::AggregateKind::Array(ty) => self.check_local_ty(ty),

            mir::AggregateKind::Tuple => {} // OK

            mir::AggregateKind::Adt(_, _, substs, _) => {
                for kind in substs.iter() {
                    match kind.unpack() {
                        ty::subst::UnpackedKind::Lifetime(..) => partially!(self, "lifetime parameters are partially supported"),

                        ty::subst::UnpackedKind::Type(ty) => self.check_local_ty(ty),
                    }
                }
            }

            mir::AggregateKind::Closure(..) => unsupported!(self, "closures are not supported"),

            mir::AggregateKind::Generator(..) => unsupported!(self, "generators are not supported"),
        }

        for operand in operands {
            self.check_operand(operand);
        }
    }
}
