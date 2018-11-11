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
use prusti_interface::environment::{ProcedureLoops, Procedure};
use rustc::mir::interpret::GlobalId;
use rustc::middle::const_val::ConstVal;

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
            unsupported!(self, "uses function calls from outer crates")
        }
    }

    fn check_fn_sig(&mut self, sig: &ty::FnSig<'tcx>) {
        requires!(self, !sig.variadic, "uses variadic functions");

        match sig.unsafety {
            hir::Unsafety::Unsafe => {
                unsupported!(self, "uses unsafe functions");
            }

            hir::Unsafety::Normal => {} // OK
        }

        for input_ty in sig.inputs() {
            self.check_input_ty(input_ty);
        }

        self.check_return_ty(sig.output());
    }

    fn check_fn_kind(&mut self, fk: FnKind<'tcx>) {
        match fk {
            FnKind::Closure(..) => {
                unsupported!(self, "uses closures");
            }

            FnKind::ItemFn(_, ref generics, header, _, _) => {
                for generic_param in generics.params.iter() {
                    match generic_param.kind {
                        hir::GenericParamKind::Type {..} => unsupported!(self, "uses function type parameters"),

                        hir::GenericParamKind::Lifetime {..} => {} // OK
                    }
                }
                requires!(self, generics.where_clause.predicates.is_empty(), "uses lifetimes constraints");
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
                unsupported!(self, "uses unsafe functions");
            }

            hir::Unsafety::Normal => {} // OK
        }

        match fh.asyncness {
            hir::IsAsync::Async => {
                unsupported!(self, "uses asynchronous functions");
            }

            hir::IsAsync::NotAsync => {} // OK
        }
    }

    fn check_input_ty(&mut self, ty: ty::Ty<'tcx>) {
        match ty.sty {
            ty::TypeVariants::TyBool => {} // OK

            ty::TypeVariants::TyChar => {} // OK

            ty::TypeVariants::TyInt(_) => {} // OK

            ty::TypeVariants::TyUint(_) => {} // OK

            ty::TypeVariants::TyRawPtr(ty::TypeAndMut { ty: inner_ty, .. }) => {
                self.check_inner_ty(inner_ty)
            }

            ty::TypeVariants::TyRef(_, inner_ty, _) => {
                self.check_inner_ty(inner_ty)
            }

            _ => unsupported!(self, "has arguments of type non-integer, non-boolean, non-char or non-reference"),
        }

        self.check_ty(ty);
    }

    fn check_return_ty(&mut self, ty: ty::Ty<'tcx>) {
        match ty.sty {
            ty::TypeVariants::TyBool => {} // OK

            ty::TypeVariants::TyChar => {} // OK

            ty::TypeVariants::TyInt(_) => {} // OK

            ty::TypeVariants::TyUint(_) => {} // OK

            _ => unsupported!(self, "has return value of type non-integer, non-boolean or non-char"),
        }

        self.check_ty(ty);
    }

    fn check_ty(&mut self, ty: ty::Ty<'tcx>) {
        match ty.sty {
            ty::TypeVariants::TyBool => {} // OK

            ty::TypeVariants::TyChar => {} // OK

            ty::TypeVariants::TyInt(_) => {} // OK

            ty::TypeVariants::TyUint(_) => {} // OK

            ty::TypeVariants::TyFloat(..) => unsupported!(self, "uses floating-point types"),

            // Structures, enumerations and unions.
            //
            // Substs here, possibly against intuition, *may* contain `TyParam`s.
            // That is, even after substitution it is possible that there are type
            // variables. This happens when the `TyAdt` corresponds to an ADT
            // definition and not a concrete use of it.
            ty::TypeVariants::TyAdt(adt_def, substs) => {
                self.check_ty_adt(adt_def, substs);
                for kind in substs.iter() {
                    match kind.unpack() {
                        ty::subst::UnpackedKind::Lifetime(..) => partially!(self, "uses data type with lifetime parameters"),

                        ty::subst::UnpackedKind::Type(ty) => self.check_ty(ty),
                    }
                }
            }

            ty::TypeVariants::TyForeign(..) => unsupported!(self, "uses foreign types"),

            ty::TypeVariants::TyStr => partially!(self, "uses `str` types"),

            ty::TypeVariants::TyArray(inner_ty, ..) => {
                self.check_inner_ty(inner_ty);
                unsupported!(self, "uses `array` types")
            }

            ty::TypeVariants::TySlice(inner_ty, ..) => {
                self.check_inner_ty(inner_ty);
                unsupported!(self, "uses `slice` types")
            }

            ty::TypeVariants::TyRawPtr(ty::TypeAndMut { ty: inner_ty, .. }) => self.check_inner_ty(inner_ty),

            ty::TypeVariants::TyRef(_, inner_ty, _) => self.check_inner_ty(inner_ty),

            ty::TypeVariants::TyFnDef(..) => unsupported!(self, "uses function types"),

            ty::TypeVariants::TyFnPtr(..) => unsupported!(self, "uses function pointer types"),

            ty::TypeVariants::TyDynamic(..) => unsupported!(self, "uses trait types"),

            ty::TypeVariants::TyClosure(..) => unsupported!(self, "uses closures"),

            ty::TypeVariants::TyGenerator(..) => unsupported!(self, "uses generators"),

            ty::TypeVariants::TyGeneratorWitness(..) => unsupported!(self, "uses generators"),

            ty::TypeVariants::TyNever => {} // OK

            ty::TypeVariants::TyTuple(inner_tys) => {
                for inner_ty in inner_tys {
                    self.check_inner_ty(inner_ty);
                }
            }

            ty::TypeVariants::TyProjection(..) => unsupported!(self, "uses associated types"),

            ty::TypeVariants::TyAnon(..) => unsupported!(self, "uses anonymized types"),

            ty::TypeVariants::TyParam(..) => unsupported!(self, "uses generic type parameters"),

            ty::TypeVariants::TyInfer(..) => unsupported!(self, "has uninferred types"),

            ty::TypeVariants::TyError => unsupported!(self, "has erroneous inferred types"),
        }
    }

    fn check_ty_adt(&mut self, adt_def: &ty::AdtDef, substs: &Substs<'tcx>) {
        requires!(self, !adt_def.is_union(), "uses union types");

        if adt_def.is_box() {
            let boxed_ty = substs.type_at(0);
            self.check_inner_ty(boxed_ty);
        } else {
            for field_def in adt_def.all_fields() {
                let field_ty = field_def.ty(self.tcx, substs);
                self.check_inner_ty(field_ty);
            }
        }
    }

    fn check_inner_ty(&mut self, ty: ty::Ty<'tcx>) {
        skip_visited_inner_type_variant!(self, &ty.sty);

        self.check_ty(ty);

        match ty.sty {
            ty::TypeVariants::TyRef(..) => partially!(self, "uses references inside data structures"),

            _ => {} // OK
        }
    }

    fn check_mir(&mut self, procedure: &Procedure<'a, 'tcx>) {
        self.check_mir_signature(procedure);

        let mir = procedure.get_mir();

        //for local_decl in &mir.local_decls {
        //    self.check_ty(local_decl.ty);
        //}

        requires!(
            self, ProcedureLoops::new(mir).count_loop_heads() == 0,
            "uses loops"
        );

        // TODO: check only blocks that may lead to a `Return` terminator
        for (index, basic_block_data) in mir.basic_blocks().iter_enumerated() {
            if !procedure.is_reachable_block(index) || procedure.is_spec_block(index) {
                continue;
            }
            for stmt in &basic_block_data.statements {
                self.check_mir_stmt(mir, stmt);
            }
            self.check_mir_terminator(mir, basic_block_data.terminator.as_ref().unwrap());
        }
    }

    fn check_mir_signature(&mut self, procedure: &Procedure<'a, 'tcx>) {
        let mir = procedure.get_mir();
        self.check_return_ty(mir.return_ty());
        requires!(self, mir.yield_ty.is_none(), "uses `yield`");
        requires!(self, mir.upvar_decls.is_empty(), "uses variables captured in closures");

        for arg_index in mir.args_iter() {
            let arg = &mir.local_decls[arg_index];
            self.check_input_ty(arg.ty);
        }
    }

    fn check_mir_stmt(&mut self, mir: &mir::Mir<'tcx>, stmt: &mir::Statement<'tcx>) {
        match stmt.kind {
            mir::StatementKind::Assign(ref place, ref rvalue) => {
                self.check_place(mir, place);
                self.check_rvalue(mir, rvalue);
            }

            mir::StatementKind::ReadForMatch(ref place) => self.check_place(mir, place),

            mir::StatementKind::SetDiscriminant { ref place, .. } => self.check_place(mir, place),

            mir::StatementKind::StorageLive(_) => {} // OK

            mir::StatementKind::StorageDead(_) => {} // OK

            mir::StatementKind::InlineAsm {..} => unsupported!(self, "uses inline Assembly"),

            mir::StatementKind::Validate(_, _) => {} // OK

            mir::StatementKind::EndRegion(_) => {} // OK

            mir::StatementKind::UserAssertTy(_, _) => {} // OK

            mir::StatementKind::Nop => {} // OK
        }
    }

    fn check_mir_terminator(&mut self, mir: &mir::Mir<'tcx>, term: &mir::Terminator<'tcx>) {
        match term.kind {
            mir::TerminatorKind::Goto {..} => {} // OK

            mir::TerminatorKind::SwitchInt { ref discr, .. } => self.check_operand(mir, discr),

            mir::TerminatorKind::Resume => {
                // This should be unreachable
                partially!(self, "uses `resume` MIR statements");
            }

            mir::TerminatorKind::Abort => {} // OK

            mir::TerminatorKind::Return => {} // OK

            mir::TerminatorKind::Unreachable => {} // OK

            mir::TerminatorKind::Drop { ref location, .. } => self.check_place(mir, location),

            mir::TerminatorKind::DropAndReplace { ref location, ref value, .. } => {
                self.check_place(mir, location);
                self.check_operand(mir, value);
            }

            mir::TerminatorKind::Call { ref func, ref args, ref destination, .. } => {
                if let mir::Operand::Constant(
                    box mir::Constant {
                        literal: mir::Literal::Value {
                            value: ty::Const {
                                ty: &ty::TyS {
                                    sty: ty::TyFnDef(def_id, ref substs),
                                    ..
                                },
                                ..
                            }
                        },
                        ..
                    }
                ) = func {
                    let proc_name: &str = &self.tcx.absolute_item_path_str(def_id);
                    match proc_name {
                        "std::rt::begin_panic" |
                        "std::panicking::begin_panic" => {} // OK

                        "<std::boxed::Box<T>>::new" => {
                            for arg in args {
                                self.check_operand(mir, arg);
                            }
                            if let Some((ref place, _)) = destination {
                                self.check_place(mir, place);
                            }
                        }

                        _ => {
                            for arg in args {
                                self.check_operand(mir, arg);
                            }
                            if let Some((ref place, _)) = destination {
                                self.check_place(mir, place);
                            }
                            for kind in substs.iter() {
                                match kind.unpack() {
                                    ty::subst::UnpackedKind::Lifetime(..) => {} // OK

                                    ty::subst::UnpackedKind::Type(ty) => self.check_ty(ty),
                                }
                            }
                            let can_build_mir = match self.tcx.hir.as_local_node_id(def_id) {
                                None => {
                                    unsupported!(
                                        self,
                                        "calls functions from an external crate"
                                    );
                                    false
                                }
                                Some(node_id) => match self.tcx.hir.get(node_id) {
                                    hir::map::NodeVariant(_) => { true } // OK
                                    hir::map::NodeStructCtor(_) => { true } // OK
                                    _ => match self.tcx.hir.maybe_body_owned_by(node_id) {
                                        Some(_) => { true } // OK
                                        None => {
                                            unsupported!(
                                                self,
                                                "calls body-less functions"
                                            );
                                            false
                                        }
                                    }
                                }
                            };
                            if can_build_mir {
                                // Check that the contract of the called function is supported
                                let procedure = Procedure::new(self.tcx, def_id);
                                self.check_mir_signature(&procedure);
                            }
                        }
                    }
                } else {
                    unsupported!(self, "uses non explicit function calls");
                }
            }

            mir::TerminatorKind::Assert { ref cond, .. } => self.check_operand(mir, cond),

            mir::TerminatorKind::Yield {..} => unsupported!(self, "uses `yield`"),

            mir::TerminatorKind::GeneratorDrop {..} => unsupported!(self, "uses `generator drop` MIR statement"),

            mir::TerminatorKind::FalseEdges {..} => {} // OK

            mir::TerminatorKind::FalseUnwind {..} => {} // OK
        }
    }

    fn get_place_ty(&self, mir: &mir::Mir<'tcx>, place: &mir::Place<'tcx>) -> ty::Ty<'tcx> {
        match place {
            mir::Place::Local(ref local) => mir.local_decls[*local].ty,

            mir::Place::Static( box mir::Static { ty, .. }) => ty,

            mir::Place::Projection(box mir::Projection { ref base, ref elem }) => {
                let base_ty = self.get_place_ty(mir, base);
                mir::tcx::PlaceTy::from_ty(base_ty).projection_ty(self.tcx, elem).to_ty(self.tcx)
            }
        }
    }

    fn get_operand_ty(&self, mir: &mir::Mir<'tcx>, operand: &mir::Operand<'tcx>) -> ty::Ty<'tcx> {
        trace!("get_operand_ty {:?}", operand);

        match operand {
            mir::Operand::Copy(ref place) |
            mir::Operand::Move(ref place) => self.get_place_ty(mir, place),

            mir::Operand::Constant(box mir::Constant { ty, .. }) => ty
        }
    }

    fn check_place(&mut self, mir: &mir::Mir<'tcx>, place: &mir::Place<'tcx>) {
        match place {
            mir::Place::Local(ref local) => {
                let local_ty = &mir.local_decls[*local].ty;
                self.check_ty(local_ty);
            }

            mir::Place::Static(..) => unsupported!(self, "uses static variables"),

            mir::Place::Projection(box ref projection) => self.check_projection(mir, projection),
        }
    }

    fn check_projection(&mut self, mir: &mir::Mir<'tcx>, projection: &mir::PlaceProjection<'tcx>) {
        self.check_place(mir, &projection.base);
        match projection.elem {
            mir::ProjectionElem::Deref => {} // OK

            mir::ProjectionElem::Field(_, ty) => self.check_inner_ty(ty),

            mir::ProjectionElem::Index(..) => unsupported!(self, "uses index operations"),

            mir::ProjectionElem::ConstantIndex {..} => unsupported!(self, "uses indices generated by slice patterns"),

            mir::ProjectionElem::Subslice {..} => unsupported!(self, "uses indices generated by slice patterns"),

            mir::ProjectionElem::Downcast(adt_def, _) => requires!(self, !adt_def.is_union(), "uses union types"),
        }
    }

    fn check_binary_op(&mut self, op: &mir::BinOp, left_ty: ty::Ty<'tcx>, right_ty: ty::Ty<'tcx>) {
        use rustc::mir::BinOp::*;
        match op {
            Add | Sub | Mul => {} // OK
            Div => {
                interesting!(self, "uses division")
            }
            Rem => {} // OK
            BitXor | BitAnd | BitOr => {
                match (&left_ty.sty, &right_ty.sty) {
                    (ty::TypeVariants::TyBool, ty::TypeVariants::TyBool) => {} // OK
                    _ => unsupported!(self, "uses bit operations for non-boolean types")
                }
            }
            Shl | Shr => unsupported!(self, "uses bit shift operations"),
            Eq | Lt | Le | Ne | Ge | Gt => {} // OK
            Offset => unsupported!(self, "uses offset operation"),
        }
    }

    fn check_unary_op(&mut self, op: &mir::UnOp, ty: ty::Ty<'tcx>) {
        use rustc::mir::UnOp::*;
        match op {
            Neg => {} // OK
            Not => {
                match &ty.sty {
                    ty::TypeVariants::TyBool => {} // OK
                    _ => unsupported!(self, "uses '!' negation for non-boolean types"),
                }
            }
        }
    }

    fn check_rvalue(&mut self, mir: &mir::Mir<'tcx>, rvalue: &mir::Rvalue<'tcx>) {
        match rvalue {
            mir::Rvalue::Use(ref operand) => self.check_operand(mir, operand),

            mir::Rvalue::Repeat(..) => unsupported!(self, "uses `repeat` operations"),

            mir::Rvalue::Ref(_, _, ref place) => self.check_place(mir, place),

            mir::Rvalue::Len(ref place) => self.check_place(mir, place),

            mir::Rvalue::Cast(..) => unsupported!(self, "uses cast operations"),

            mir::Rvalue::BinaryOp(ref op, ref left_operand, ref right_operand) => {
                let left_ty = self.get_operand_ty(mir, left_operand);
                let right_ty = self.get_operand_ty(mir, right_operand);
                self.check_binary_op(op, left_ty, right_ty);
                self.check_operand(mir, left_operand);
                self.check_operand(mir, right_operand);
            }

            mir::Rvalue::CheckedBinaryOp(ref op, ref left_operand, ref right_operand) => {
                let left_ty = self.get_operand_ty(mir, left_operand);
                let right_ty = self.get_operand_ty(mir, right_operand);
                self.check_binary_op(op, left_ty, right_ty);
                self.check_operand(mir, left_operand);
                self.check_operand(mir, right_operand);
            }

            mir::Rvalue::UnaryOp(ref op, ref operand) => {
                let ty = self.get_operand_ty(mir, operand);
                self.check_unary_op(op, ty);
                self.check_operand(mir, operand)
            }

            mir::Rvalue::NullaryOp(mir::NullOp::Box, ty) => self.check_inner_ty(ty),

            mir::Rvalue::NullaryOp(mir::NullOp::SizeOf, _) => unsupported!(self, "uses `sizeof` operations"),

            mir::Rvalue::Discriminant(ref place) => self.check_place(mir, place),

            mir::Rvalue::Aggregate(box ref kind, ref operands) => self.check_aggregate(mir, kind, operands),
        }
    }

    fn check_operand(&mut self, mir: &mir::Mir<'tcx>, operand: &mir::Operand<'tcx>) {
        match operand {
            mir::Operand::Copy(ref place) |
            mir::Operand::Move(ref place) => {
                self.check_place(mir, place)
            }

            mir::Operand::Constant(box mir::Constant { ty, ref literal, .. }) => {
                self.check_literal(literal);
                self.check_ty(ty);
            }
        }
    }

    fn check_literal(&mut self, literal: &mir::Literal<'tcx>) {
        trace!("check_literal {:?}", literal);

        match literal {
            mir::Literal::Value { value } => {
                match value.val {
                    ConstVal::Value(ref value) => {
                        requires!(self, value.to_scalar().is_some(), "uses non-scalar literals");
                    }
                    ConstVal::Unevaluated(def_id, substs) => {
                        // On crate `078_crossbeam` the `const_eval` call fails with
                        // "can't type-check body of DefId(0/0:18 ~ lock_api[964c]::mutex[0]::RawMutex[0]::INIT[0])"
                        // at "const INIT: Self;"
                        partially!(self, "uses unevaluated constants");
                        /*
                        let param_env = self.tcx.param_env(def_id);
                        let cid = GlobalId {
                            instance: ty::Instance::new(def_id, substs),
                            promoted: None
                        };
                        if let Ok(const_value) = self.tcx.const_eval(param_env.and(cid)) {
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

                self.check_ty(value.ty);

                match value.ty.sty {
                    ty::TypeVariants::TyBool |
                    ty::TypeVariants::TyInt(_) |
                    ty::TypeVariants::TyUint(_) |
                    ty::TypeVariants::TyChar => {} // OK

                    _ => unsupported!(self, "uses literals of type non-boolean, non-integer or non-char")
                };
            }
            mir::Literal::Promoted { .. } => partially!(self, "uses promoted constant literals")
        }
    }

    fn check_aggregate(&mut self, mir: &mir::Mir<'tcx>, kind: &mir::AggregateKind<'tcx>, operands: &Vec<mir::Operand<'tcx>>) {
        trace!("check_aggregate {:?}, {:?}", kind, operands);

        match kind {
            mir::AggregateKind::Array(ty) => {
                unsupported!(self, "uses arrays");
                self.check_inner_ty(ty)
            }

            mir::AggregateKind::Tuple => {} // OK

            mir::AggregateKind::Adt(_, _, substs, _) => {
                for kind in substs.iter() {
                    match kind.unpack() {
                        ty::subst::UnpackedKind::Lifetime(..) => partially!(self, "uses data structures with lifetime parameters"),

                        ty::subst::UnpackedKind::Type(ty) => self.check_inner_ty(ty),
                    }
                }
            }

            mir::AggregateKind::Closure(..) => unsupported!(self, "uses closures"),

            mir::AggregateKind::Generator(..) => unsupported!(self, "uses generators"),
        }

        for operand in operands {
            self.check_operand(mir, operand);
        }
    }
}
