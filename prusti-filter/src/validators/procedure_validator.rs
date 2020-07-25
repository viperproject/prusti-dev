// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_interface::environment::{Procedure, ProcedureLoops};
use rustc::hir;
use rustc::hir::def_id::DefId;
use rustc_middle::mir;
use rustc::ty;
use std::collections::{HashSet, HashMap};
use syntax::codemap::Span;
use validators::common_validator::CommonValidator;
use validators::unsafety_validator::contains_unsafe;
use validators::Reason;
use validators::SupportStatus;

pub struct ProcedureValidator<'a, 'tcx: 'a> {
    tcx: ty::TyCtxt<'tcx>,
    support: SupportStatus,
    visited_return_type_variants: HashSet<&'tcx ty::TypeVariants<'tcx>>,
    visited_inner_type_variants: HashSet<&'tcx ty::TypeVariants<'tcx>>,
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

impl<'a, 'tcx: 'a> CommonValidator<'a, 'tcx> for ProcedureValidator<'a, 'tcx> {
    fn support(&mut self) -> &mut SupportStatus {
        &mut self.support
    }

    fn get_support_status(self) -> SupportStatus {
        self.support
    }

    fn tcx(&self) -> ty::TyCtxt<'tcx> {
        self.tcx
    }

    fn check_inner_ty(&mut self, ty: ty::Ty<'tcx>, span: Span) {
        skip_visited_inner_type_variant!(self, &ty.sty);

        self.check_ty(ty, span);

        match ty.sty {
            ty::TypeVariants::TyRef(..) => partially!(self, span, "uses reference-typed fields"),

            _ => {} // OK
        }
    }
}

impl<'a, 'tcx: 'a> ProcedureValidator<'a, 'tcx> {
    pub fn new(tcx: ty::TyCtxt<'tcx>) -> Self {
        ProcedureValidator {
            tcx,
            support: SupportStatus::new(),
            visited_return_type_variants: HashSet::new(),
            visited_inner_type_variants: HashSet::new(),
        }
    }

    pub fn check(&mut self, def_id: DefId) {
        let node_id = self.tcx.hir.as_local_node_id(def_id).unwrap();
        let span = self.tcx.def_span(def_id);

        let sig = self.tcx.fn_sig(def_id);
        self.check_fn_sig(sig.skip_binder(), def_id);

        let fn_node = self.tcx.hir.get(node_id);
        self.check_hir(fn_node);

        if contains_unsafe(self.tcx, node_id) {
            unsupported!(self, span, "contains unsafe code");
        }

        let procedure = Procedure::new(self.tcx, def_id);
        self.check_mir(&procedure);
    }

    fn check_fn_sig(&mut self, sig: &ty::FnSig<'tcx>, def_id: DefId) {
        let span = self.tcx.def_span(def_id);

        if sig.variadic {
            unsupported!(self, span, "is a C-variadic function");
        }

        match sig.unsafety {
            hir::Unsafety::Unsafe => {
                unsupported!(self, span, "is an unsafe function");
            }

            hir::Unsafety::Normal => {} // OK
        }

        // Note: the types are already checked from MIR

        self.inspect_return_ty(sig.output());
    }

    /// Just used to look for "interesting" info
    fn inspect_return_ty(&mut self, ty: ty::Ty<'tcx>) {
        skip_visited_return_type_variant!(self, &ty.sty);

        match ty.sty {
            ty::TypeVariants::TyRef(_, inner_ty, hir::MutMutable) => {
                interesting!(self, "has mutable reference in return type");
                self.inspect_return_ty(inner_ty);
            }

            ty::TypeVariants::TyRef(_, inner_ty, hir::MutImmutable) => {
                interesting!(self, "has immutable reference in return type");
                self.inspect_return_ty(inner_ty);
            }

            ty::TypeVariants::TyRawPtr(ty::TypeAndMut { ty: inner_ty, .. }) => {
                self.inspect_return_ty(inner_ty);
            }

            // Structures, enumerations and unions.
            ty::TypeVariants::TyAdt(adt_def, substs) => {
                for field_def in adt_def.all_fields() {
                    let field_ty = field_def.ty(self.tcx, substs);
                    self.inspect_return_ty(field_ty);
                }
            }

            ty::TypeVariants::TyArray(inner_ty, ..) => {
                self.inspect_return_ty(inner_ty);
            }

            ty::TypeVariants::TySlice(inner_ty, ..) => {
                self.inspect_return_ty(inner_ty);
            }

            ty::TypeVariants::TyTuple(inner_tys) => {
                for inner_ty in inner_tys {
                    self.inspect_return_ty(inner_ty);
                }
            }

            _ => {} // Nothing
        }
    }

    fn check_mir(&mut self, procedure: &Procedure<'a, 'tcx>) {
        self.check_mir_signature(procedure);
        self.check_loops(procedure);

        let mir = procedure.get_mir();

        //for local_decl in &mir.local_decls {
        //    self.check_ty(local_decl.ty, local_decl.source_info.span);
        //}

        for (bbi, basic_block_data) in mir.basic_blocks().iter_enumerated() {
            if !procedure.is_reachable_block(bbi) || procedure.is_spec_block(bbi) {
                continue;
            }
            if !procedure.is_panic_block(bbi) {
                for stmt in &basic_block_data.statements {
                    self.check_mir_stmt(mir, stmt);
                }
            }
            self.check_mir_terminator(mir, basic_block_data.terminator());
        }
    }

    fn check_mir_signature(&mut self, procedure: &Procedure<'a, 'tcx>) {
        let mir = procedure.get_mir();
        let span = procedure.get_span();

        self.check_ty(mir.return_ty(), span);

        if !mir.yield_ty.is_none() {
            unsupported!(self, span, "uses `yield`");
        }
        if !mir.upvar_decls.is_empty() {
            unsupported!(self, span, "uses variables captured in closures");
        }

        for arg_index in mir.args_iter() {
            let arg = &mir.local_decls[arg_index];
            self.check_mir_arg(arg);
        }
    }

    fn check_loops(&mut self, procedure: &Procedure<'a, 'tcx>) {
        let mir = procedure.get_mir();
        let loops = ProcedureLoops::new(mir);
        let mut reborrowing_hints: HashMap<mir::Local, HashMap<usize, HashSet<Span>>> = HashMap::new();

        for (bbi, basic_block_data) in mir.basic_blocks().iter_enumerated() {
            if !procedure.is_reachable_block(bbi) || procedure.is_spec_block(bbi) {
                continue;
            }

            // Detect likely reborrowing
            if !procedure.is_panic_block(bbi) {
                let loop_depth = if let Some(loop_head) = loops.get_loop_head(bbi) {
                    loops.get_loop_head_depth(loop_head)
                } else {
                    0
                };
                for stmt in &basic_block_data.statements {
                    if let mir::StatementKind::Assign(ref lhs_place, _) = stmt.kind {
                        if let mir::Place::Local(place_base) = lhs_place { // TODO: is this enough?
                            let lhs_ty = self.get_place_ty(mir, lhs_place);
                            if let ty::TypeVariants::TyRef(_, _, _) = lhs_ty.sty {
                                // may reborrow inside a loop
                                let local_levels = reborrowing_hints
                                    .entry(*place_base)
                                    .or_insert(HashMap::new());
                                let spans = local_levels.entry(loop_depth)
                                    .or_insert(HashSet::new());
                                spans.insert(stmt.source_info.span);
                            }
                        }
                    }
                }
                let term = basic_block_data.terminator();
                match term.kind {
                    mir::TerminatorKind::DropAndReplace { location: ref lhs_place, .. } |
                    mir::TerminatorKind::Call { destination: Some((ref lhs_place, _)), .. } => {
                        if let mir::Place::Local(place_base) = lhs_place { // TODO: is this enough?
                            let lhs_ty = self.get_place_ty(mir, lhs_place);
                            if let ty::TypeVariants::TyRef(_, _, _) = lhs_ty.sty {
                                // may reborrow inside a loop
                                let local_levels = reborrowing_hints
                                    .entry(*place_base)
                                    .or_insert(HashMap::new());
                                let spans = local_levels.entry(loop_depth)
                                    .or_insert(HashSet::new());
                                spans.insert(term.source_info.span);
                            }
                        }
                    }

                    _ => {} // OK
                }
            }

            // Detect return, break, continue inside loops
            for successor in basic_block_data.terminator().successors() {
                if !procedure.is_reachable_block(*successor) || procedure.is_spec_block(*successor)
                {
                    continue;
                }
                let _successor_data = &mir.basic_blocks()[*successor];
                // TODO: enable only after issue #149 is solved
                //if let mir::TerminatorKind::Unreachable = successor_data.terminator().kind {
                //    continue;
                //}
                //if !procedure.is_panic_block(successor) {
                //    continue;
                //}
            }
        }

        for (_, local_levels) in &reborrowing_hints {
            if local_levels.keys().len() > 1 {
                for (level, spans) in local_levels {
                    if *level > 0 {
                        for span in spans {
                            partially!(self, *span, "may reborrow inside a loop");
                        }
                    }
                }
            }
        }
    }

    fn check_mir_arg(&mut self, arg: &mir::LocalDecl<'tcx>) {
        let span = arg.source_info.span;

        self.check_ty(arg.ty, span);

        match arg.mutability {
            mir::Mutability::Mut => partially!(self, span, "uses mutable arguments"),

            mir::Mutability::Not => {} // OK
        }
    }
}
