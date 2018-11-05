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
use rustc::mir::interpret::GlobalId;
use rustc::middle::const_val::ConstVal;

pub struct ProcedureValidator<'a, 'tcx: 'a> {
    tcx: ty::TyCtxt<'a, 'tcx, 'tcx>,
    support: SupportStatus,
    visited_return_type_variants: HashSet<&'tcx ty::TypeVariants<'tcx>>,
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

macro_rules! skip_visited_return_type_variant {
    ($self:expr, $tv:expr) => {
        if $self.visited_return_type_variants.contains(&$tv) {
            return;
        } else {
            $self.visited_return_type_variants.insert($tv);
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

impl<'a, 'tcx: 'a> ProcedureValidator<'a, 'tcx> {
    pub fn new(tcx: ty::TyCtxt<'a, 'tcx, 'tcx>) -> Self {
        ProcedureValidator {
            tcx,
            support: SupportStatus::new(),
            visited_return_type_variants: HashSet::new(),
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
            unsupported!(self, "function calls to outer crates are unsupported")
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
            self.check_ty(input_ty, "argument type");
        }

        self.check_ty(sig.output(), "return type");
        self.check_return_ty(sig.output());
    }

    /// Just used to look for "interesting" info
    fn check_return_ty(&mut self, ty: ty::Ty<'tcx>) {
        skip_visited_return_type_variant!(self, &ty.sty);

        match ty.sty {
            ty::TypeVariants::TyRef(_, inner_ty, hir::MutMutable) => {
                interesting!(self, "mutable reference in return type");
                self.check_return_ty(inner_ty);
            }

            ty::TypeVariants::TyRef(_, inner_ty, hir::MutImmutable) => {
                interesting!(self, "immutable reference in return type");
                self.check_return_ty(inner_ty);
            }

            ty::TypeVariants::TyRawPtr(ty::TypeAndMut { ty: inner_ty, .. }) => {
                self.check_return_ty(inner_ty);
            },

            // Structures, enumerations and unions.
            ty::TypeVariants::TyAdt(adt_def, substs) => {
                for field_def in adt_def.all_fields() {
                    let field_ty = field_def.ty(self.tcx, substs);
                    self.check_return_ty(field_ty);
                }
            },

            ty::TypeVariants::TyArray(inner_ty, ..) => {
                self.check_return_ty(inner_ty);
            },

            ty::TypeVariants::TySlice(inner_ty, ..) => {
                self.check_return_ty(inner_ty);
            },

            ty::TypeVariants::TyTuple(inner_tys) => {
                for inner_ty in inner_tys {
                    self.check_return_ty(inner_ty);
                }
            }

            _ => {} // Nothing
        }
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

    fn check_ty(&mut self, ty: ty::Ty<'tcx>, pos: &str) {
        match ty.sty {
            ty::TypeVariants::TyBool => {} // OK

            ty::TypeVariants::TyChar => {} // OK

            ty::TypeVariants::TyInt(_) => {} // OK

            ty::TypeVariants::TyUint(_) => {} // OK

            ty::TypeVariants::TyFloat(..) => unsupported_pos!(self, pos, "floating-point types are not supported"),

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
                        ty::subst::UnpackedKind::Lifetime(..) => partially!(self, "lifetime parameters are partially supported"),

                        ty::subst::UnpackedKind::Type(ty) => self.check_ty(ty, "adt"),
                    }
                }
            },

            ty::TypeVariants::TyForeign(..) => unsupported_pos!(self, pos, "foreign types are not supported"),

            ty::TypeVariants::TyStr => partially_pos!(self, pos, "`str` types are partially supported"),

            ty::TypeVariants::TyArray(inner_ty, ..) => {
                self.check_inner_ty(inner_ty, pos);
                unsupported_pos!(self, pos, "`array` types are not supported")
            },

            ty::TypeVariants::TySlice(inner_ty, ..) => {
                self.check_inner_ty(inner_ty, pos);
                unsupported_pos!(self, pos, "`slice` types are not supported")
            },

            ty::TypeVariants::TyRawPtr(ty::TypeAndMut { mutbl: hir::MutMutable, ty: inner_ty }) => self.check_inner_ty(inner_ty, pos),

            ty::TypeVariants::TyRawPtr(ty::TypeAndMut { mutbl: hir::MutImmutable, ty: inner_ty }) => {
                partially_pos!(self, pos, "shared raw pointers are partially supported");
                self.check_inner_ty(inner_ty, pos);
            },

            ty::TypeVariants::TyRef(_, inner_ty, hir::MutMutable) => self.check_inner_ty(inner_ty, pos),

            ty::TypeVariants::TyRef(_, inner_ty, hir::MutImmutable) => {
                partially_pos!(self, pos, "shared references are partially supported");
                self.check_inner_ty(inner_ty, pos);
            },

            ty::TypeVariants::TyFnDef(..) => unsupported_pos!(self, pos, "function types are not supported"),

            ty::TypeVariants::TyFnPtr(..) => unsupported_pos!(self, pos, "function pointer types are not supported"),

            ty::TypeVariants::TyDynamic(..) => unsupported_pos!(self, pos, "trait types are not supported"),

            ty::TypeVariants::TyClosure(..) => unsupported_pos!(self, pos, "closures are not supported"),

            ty::TypeVariants::TyGenerator(..) => unsupported_pos!(self, pos, "generators are not supported"),

            ty::TypeVariants::TyGeneratorWitness(..) => unsupported_pos!(self, pos, "types inside generators are not supported"),

            ty::TypeVariants::TyNever => {}, // OK

            ty::TypeVariants::TyTuple(inner_tys) => {
                for inner_ty in inner_tys {
                    self.check_inner_ty(inner_ty, pos);
                }
            }

            ty::TypeVariants::TyProjection(..) => unsupported_pos!(self, pos, "associated types are not supported"),

            ty::TypeVariants::TyAnon(..) => unsupported_pos!(self, pos, "anonymized types are not supported"),

            ty::TypeVariants::TyParam(..) => unsupported_pos!(self, pos, "generic type parameters are not supported"),

            ty::TypeVariants::TyInfer(..) => unsupported_pos!(self, pos, "uninferred types are not supported"),

            ty::TypeVariants::TyError => unsupported_pos!(self, pos, "erroneous inferred types are not supported"),
        }
    }

    fn check_ty_adt(&mut self, adt_def: &ty::AdtDef, substs: &Substs<'tcx>) {
        requires!(self, !adt_def.is_union(), "union types are not supported");

        if adt_def.is_box() {
            let boxed_ty = substs.type_at(0);
            self.check_inner_ty(boxed_ty, "box");
        } else {
            for field_def in adt_def.all_fields() {
                let field_ty = field_def.ty(self.tcx, substs);
                self.check_inner_ty(field_ty, "adt");
            }
        }
    }

    fn check_inner_ty(&mut self, ty: ty::Ty<'tcx>, pos: &str) {
        skip_visited_inner_type_variant!(self, &ty.sty);

        self.check_ty(ty, pos);

        match ty.sty {
            ty::TypeVariants::TyRef(..) => partially_pos!(self, pos, "references inside data structures are partially supported"),

            _ => {} // OK
        }
    }

    fn check_mir(&mut self, procedure: &Procedure<'a, 'tcx>) {
        self.check_mir_signature(procedure);

        //for local_decl in &mir.local_decls {
        //    self.check_ty(local_decl.ty, "local variable");
        //}

        let mir = procedure.get_mir();
        for (bbi, basic_block_data) in mir.basic_blocks().iter_enumerated() {
            if !procedure.is_reachable_block(bbi) || procedure.is_spec_block(bbi) {
                continue;
            }
            if !procedure.is_panic_block(bbi) {
                for stmt in &basic_block_data.statements {
                    self.check_mir_stmt(mir, stmt);
                }
            }
            self.check_mir_terminator(mir, basic_block_data.terminator.as_ref().unwrap());
        }
    }

    fn check_mir_signature(&mut self, procedure: &Procedure<'a, 'tcx>) {
        let mir = procedure.get_mir();
        self.check_ty(mir.return_ty(), "return type");
        requires!(self, mir.yield_ty.is_none(), "`yield` is not supported");
        requires!(self, mir.upvar_decls.is_empty(), "variables captured in closures are not supported");

        for arg_index in mir.args_iter() {
            let arg = &mir.local_decls[arg_index];
            match arg.mutability {
                mir::Mutability::Mut => partially!(self, "mutable arguments are partially supported"),

                mir::Mutability::Not => {} // OK
            }
            self.check_mir_arg(arg);
        }
    }

    fn check_mir_arg(&mut self, arg: &mir::LocalDecl<'tcx>) {
        self.check_ty(arg.ty, "argument type");
        match arg.mutability {
            mir::Mutability::Mut => partially!(self, "mutable arguments are partially supported"),

            mir::Mutability::Not => {} // OK
        }
    }

    fn check_mir_stmt(&mut self, mir: &mir::Mir<'tcx>, stmt: &mir::Statement<'tcx>) {
        trace!("check_mir_stmt {:?}", stmt);

        match stmt.kind {
            mir::StatementKind::Assign(ref place, ref rvalue) => {
                self.check_place(mir, place);
                self.check_rvalue(mir, rvalue);
            },

            mir::StatementKind::ReadForMatch(ref place) => self.check_place(mir, place),

            mir::StatementKind::SetDiscriminant { ref place, .. } => self.check_place(mir, place),

            mir::StatementKind::StorageLive(_) => {} // OK

            mir::StatementKind::StorageDead(_) => {} // OK

            mir::StatementKind::InlineAsm {..} => unsupported!(self, "inline Assembly is not supported"),

            mir::StatementKind::Validate(_, _) => {} // OK

            mir::StatementKind::EndRegion(_) => {} // OK

            mir::StatementKind::UserAssertTy(_, _) => {} // OK

            mir::StatementKind::Nop => {} // OK
        }
    }

    fn check_mir_terminator(&mut self, mir: &mir::Mir<'tcx>, term: &mir::Terminator<'tcx>) {
        trace!("check_mir_terminator {:?}", term);

        match term.kind {
            mir::TerminatorKind::Goto {..} => {} // OK

            mir::TerminatorKind::SwitchInt { ref discr, .. } => self.check_operand(mir, discr),

            mir::TerminatorKind::Resume => {
                // This should be unreachable
                partially!(self, "`resume` MIR statements are partially supported");
            },

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
                                    sty: ty::TyFnDef(def_id, ..),
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
                            let can_build_mir = match self.tcx.hir.as_local_node_id(def_id) {
                                None => {
                                    unsupported!(
                                        self,
                                        "calling functions from an external crate is not supported"
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
                                                "calling body-less functions is not supported"
                                            );
                                            false
                                        },
                                    },
                                },
                            };
                            if can_build_mir {
                                // Check that the contract of the called function is supported
                                let procedure = Procedure::new(self.tcx, def_id);
                                self.check_mir_signature(&procedure);
                            }
                        },
                    }
                } else {
                    unsupported!(self, "non explicit function calls are not supported");
                }
            }

            mir::TerminatorKind::Assert { ref cond, .. } => self.check_operand(mir, cond),

            mir::TerminatorKind::Yield {..} => unsupported!(self, "`yield` MIR statement is not supported"),

            mir::TerminatorKind::GeneratorDrop {..} => unsupported!(self, "`generator drop` MIR statement is not supported"),

            mir::TerminatorKind::FalseEdges {..} => {} // OK

            mir::TerminatorKind::FalseUnwind {..} => {} // OK
        }
    }

    fn check_place(&mut self, mir: &mir::Mir<'tcx>, place: &mir::Place<'tcx>) {
        match place {
            mir::Place::Local(ref local) => {
                let local_ty = &mir.local_decls[*local].ty;
                self.check_ty(local_ty, "MIR place");
            }

            mir::Place::Static(..) => unsupported!(self, "static variables are not supported"),

            mir::Place::Projection(box ref projection) => self.check_projection(mir, projection),
        }
    }

    fn check_projection(&mut self, mir: &mir::Mir<'tcx>, projection: &mir::PlaceProjection<'tcx>) {
        self.check_place(mir, &projection.base);
        match projection.elem {
            mir::ProjectionElem::Deref => {} // OK

            mir::ProjectionElem::Field(_, ty) => self.check_inner_ty(ty, "statement"),

            mir::ProjectionElem::Index(..) => unsupported!(self, "index operations are not supported"),

            mir::ProjectionElem::ConstantIndex {..} => unsupported!(self, "indices generated by slice patterns are not supported"),

            mir::ProjectionElem::Subslice {..} => unsupported!(self, "indices generated by slice patterns are not supported"),

            mir::ProjectionElem::Downcast(adt_def, _) => requires!(self, !adt_def.is_union(), "union types are not supported"),
        }
    }

    fn check_binary_op(&mut self, op: &mir::BinOp) {
        use rustc::mir::BinOp::*;
        match op {
            Add | Sub | Mul => {}, // OK
            Div | Rem => {}, // OK
            BitXor | BitAnd | BitOr => partially!(self, "bit operations are partially supported"),
            Shl | Shr => unsupported!(self, "bit shift operations are not supported"),
            Eq | Lt | Le | Ne | Ge | Gt => {}, // OK
            Offset => unsupported!(self, "offset operation is not supported"),
        }
    }

    fn check_unary_op(&mut self, op: &mir::UnOp) {
        use rustc::mir::UnOp::*;
        match op {
            Neg => {}, // OK
            Not => partially!(self, "bit negation is partially supported"),
        }
    }

    fn check_rvalue(&mut self, mir: &mir::Mir<'tcx>, rvalue: &mir::Rvalue<'tcx>) {
        match rvalue {
            mir::Rvalue::Use(ref operand) => self.check_operand(mir, operand),

            mir::Rvalue::Repeat(..) => unsupported!(self, "`repeat` operations are not supported"),

            mir::Rvalue::Ref(_, mir::BorrowKind::Shared, ref place) => {
                partially!(self, "shared references are partially supported");
                self.check_place(mir, place);
            },

            mir::Rvalue::Ref(_, mir::BorrowKind::Unique, ref place) => self.check_place(mir, place),

            mir::Rvalue::Ref(_, mir::BorrowKind::Mut {..}, ref place) => self.check_place(mir, place),

            mir::Rvalue::Len(..) => unsupported!(self, "length operations are not supported"),

            mir::Rvalue::Cast(..) => unsupported!(self, "cast operations are not supported"),

            mir::Rvalue::BinaryOp(ref op, ref left_operand, ref right_operand) => {
                self.check_binary_op(op);
                self.check_operand(mir, left_operand);
                self.check_operand(mir, right_operand);
            }

            mir::Rvalue::CheckedBinaryOp(ref op, ref left_operand, ref right_operand) => {
                self.check_binary_op(op);
                self.check_operand(mir, left_operand);
                self.check_operand(mir, right_operand);
            }

            mir::Rvalue::NullaryOp(mir::NullOp::Box, ty) => self.check_inner_ty(ty, "assignment of box"),

            mir::Rvalue::NullaryOp(mir::NullOp::SizeOf, _) => unsupported!(self, "`sizeof` operations are not supported"),

            mir::Rvalue::UnaryOp(ref op, ref operand) => {
                self.check_unary_op(op);
                self.check_operand(mir, operand)
            },

            mir::Rvalue::Discriminant(ref place) => self.check_place(mir, place),

            mir::Rvalue::Aggregate(box ref kind, ref operands) => self.check_aggregate(mir, kind, operands),
        }
    }

    fn check_operand(&mut self, mir: &mir::Mir<'tcx>, operand: &mir::Operand<'tcx>) {
        trace!("check_operand {:?}", operand);

        match operand {
            mir::Operand::Copy(ref place) |
            mir::Operand::Move(ref place) => self.check_place(mir, place),

            mir::Operand::Constant(box mir::Constant { ty, ref literal, .. }) => {
                self.check_literal(literal);
                self.check_ty(ty, "operand");
            }
        }
    }

    fn check_literal(&mut self, literal: &mir::Literal<'tcx>) {
        trace!("check_literal {:?}", literal);

        match literal {
            mir::Literal::Value { value } => {
                match value.val {
                    ConstVal::Value(ref value) => {
                        requires!(self, value.to_scalar().is_some(), "non-scalar literals are not supported");
                    },
                    ConstVal::Unevaluated(def_id, substs) => {
                        // On crate `078_crossbeam` the `const_eval` call fails with
                        // "can't type-check body of DefId(0/0:18 ~ lock_api[964c]::mutex[0]::RawMutex[0]::INIT[0])"
                        // at "const INIT: Self;"
                        partially!(self, "unevaluated constant are partially supported");
                        /*
                        let param_env = self.tcx.param_env(def_id);
                        let cid = GlobalId {
                            instance: ty::Instance::new(def_id, substs),
                            promoted: None
                        };
                        if let Ok(const_value) = self.tcx.const_eval(param_env.and(cid)) {
                            if let ConstVal::Value(ref value) = const_value.val {
                                requires!(self, value.to_scalar().is_some(), "non-scalar literals are not supported");
                            } else {
                                // This should be unreachable
                                unsupported!(self, "erroneous unevaluated literals are not supported")
                            }
                        } else {
                            // This should be unreachable
                            unsupported!(self, "erroneous unevaluated literals are not supported")
                        }
                        */
                    }
                };

                self.check_ty(value.ty, "constant literal");

                match value.ty.sty {
                    ty::TypeVariants::TyBool |
                    ty::TypeVariants::TyInt(_) |
                    ty::TypeVariants::TyUint(_) |
                    ty::TypeVariants::TyChar => {} // OK

                    _ => unsupported!(self, "only literals of type boolean, integer or char are supported")
                };
            }
            mir::Literal::Promoted { .. } => partially!(self, "promoted constant literals are partially supported")
        }
    }

    fn check_aggregate(&mut self, mir: &mir::Mir<'tcx>, kind: &mir::AggregateKind<'tcx>, operands: &Vec<mir::Operand<'tcx>>) {
        trace!("check_aggregate {:?}, {:?}", kind, operands);

        match kind {
            mir::AggregateKind::Array(ty) => {
                unsupported!(self, "arrays are not supported");
                self.check_ty(ty, "assignment")
            },

            mir::AggregateKind::Tuple => {} // OK

            mir::AggregateKind::Adt(_, _, substs, _) => {
                for kind in substs.iter() {
                    match kind.unpack() {
                        ty::subst::UnpackedKind::Lifetime(..) => partially!(self, "lifetime parameters are partially supported"),

                        ty::subst::UnpackedKind::Type(ty) => self.check_ty(ty, "assignment"),
                    }
                }
            }

            mir::AggregateKind::Closure(..) => unsupported!(self, "closures are not supported"),

            mir::AggregateKind::Generator(..) => unsupported!(self, "generators are not supported"),
        }

        for operand in operands {
            self.check_operand(mir, operand);
        }
    }
}
