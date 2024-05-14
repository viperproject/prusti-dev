use mir_state_analysis::{
    free_pcs::{CapabilityKind, FreePcsAnalysis, FreePcsBasicBlock, FreePcsLocation, RepackOp},
    utils::Place,
};
use prusti_rustc_interface::{
    abi,
    middle::{
        mir,
        ty::{GenericArgs, TyKind},
    },
    span::def_id::DefId,
};
//use mir_ssa_analysis::{
//    SsaAnalysis,
//};
use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::{MethodIdent, UnknownArity};

pub struct MirImpureEnc;

#[derive(Clone, Debug)]
pub enum MirImpureEncError {
    Unsupported,
}

#[derive(Clone, Debug)]
pub struct MirImpureEncOutputRef<'vir> {
    pub method_ref: MethodIdent<'vir, UnknownArity<'vir>>,
}
impl<'vir> task_encoder::OutputRefAny for MirImpureEncOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct MirImpureEncOutput<'vir> {
    pub method: vir::Method<'vir>,
}

use crate::{
    encoder_traits::{impure_function_enc::{
        ImpureFunctionEncOutput, ImpureFunctionEncOutputRef,
    }, pure_func_app_enc::PureFuncAppEnc},
    encoders::{
        self,
        lifted::{
            aggregate_cast::{
                AggregateSnapArgsCastEnc,
                AggregateSnapArgsCastEncTask
            },
            func_app_ty_params::LiftedFuncAppTyParamsEnc
        },
        FunctionCallTaskDescription, MirBuiltinEnc
    }
};

use super::{
    lifted::{
        cast::{CastArgs, CastToEnc},
        casters::CastTypeImpure,
        rust_ty_cast::RustTyCastersEnc
    },
    rust_ty_predicates::RustTyPredicatesEnc,
    ConstEnc,
    MirMonoImpureEnc,
    MirPolyImpureEnc
};

const ENCODE_REACH_BB: bool = false;

impl MirImpureEnc {
    pub fn monomorphize() -> bool {
        cfg!(feature = "mono_function_encoding")
    }
}

impl TaskEncoder for MirImpureEnc {
    task_encoder::encoder_cache!(MirImpureEnc);

    type TaskDescription<'tcx> = FunctionCallTaskDescription<'tcx>;

    type OutputRef<'vir> = ImpureFunctionEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = ImpureFunctionEncOutput<'vir>;

    type EncodingError = MirImpureEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'tcx: 'vir, 'vir>(
        task_key: &Self::TaskKey<'tcx>,
        deps: &mut TaskEncoderDependencies<'vir>,
    ) -> Result<
        (
            Self::OutputFullLocal<'vir>,
            Self::OutputFullDependency<'vir>,
        ),
        (
            Self::EncodingError,
            Option<Self::OutputFullDependency<'vir>>,
        ),
    > {
        let monomorphize = Self::monomorphize();
        let output_ref = if monomorphize {
            deps.require_ref::<MirMonoImpureEnc>(*task_key).unwrap()
        } else {
            deps.require_ref::<MirPolyImpureEnc>(task_key.def_id).unwrap()
        };
        deps.emit_output_ref::<Self>(*task_key, output_ref);
        let output: ImpureFunctionEncOutput<'_> = if monomorphize {
            deps.require_local::<MirMonoImpureEnc>(*task_key).unwrap()
        } else {
            deps.require_local::<MirPolyImpureEnc>(task_key.def_id).unwrap()
        };
        Ok((output, ()))
    }
}

pub struct ImpureEncVisitor<'tcx, 'vir, 'enc>
    where 'vir: 'enc
{
    pub vcx: &'vir vir::VirCtxt<'tcx>,
    // Are we monomorphizing functions?
    pub monomorphize: bool,
    pub deps: &'enc mut TaskEncoderDependencies<'vir>,
    pub def_id: DefId,
    pub local_decls: &'enc mir::LocalDecls<'tcx>,
    //ssa_analysis: SsaAnalysis,
    pub fpcs_analysis: FreePcsAnalysis<'enc, 'tcx>,
    pub local_defs: crate::encoders::MirLocalDefEncOutput<'vir>,

    pub tmp_ctr: usize,

    // for the current basic block
    pub current_fpcs: Option<FreePcsBasicBlock<'tcx>>,

    pub current_stmts: Option<Vec<vir::Stmt<'vir>>>,
    pub current_terminator: Option<vir::TerminatorStmt<'vir>>,

    pub encoded_blocks: Vec<vir::CfgBlock<'vir>>, // TODO: use IndexVec ?
}

impl<'tcx: 'vir, 'vir> PureFuncAppEnc<'tcx, 'vir> for ImpureEncVisitor<'tcx, 'vir, '_> {
    type EncodeOperandArgs = ();
    type Curr = !;
    type Next = !;
    type LocalDeclsSrc = mir::LocalDecls<'tcx>;
    fn vcx(&self) -> &'vir vir::VirCtxt<'tcx> {
        self.vcx
    }

    fn deps(&mut self) -> &mut TaskEncoderDependencies<'vir> {
        self.deps
    }

    fn local_decls_src(&self) -> &Self::LocalDeclsSrc {
        self.local_decls
    }

    fn encode_operand(
        &mut self,
        _args: &Self::EncodeOperandArgs,
        operand: &mir::Operand<'tcx>,
    ) -> vir::ExprGen<'vir, Self::Curr, Self::Next> {
        self.encode_operand_snap(operand)
    }

    fn monomorphize(&self) -> bool {
        self.monomorphize
    }
}

struct EncodePlaceResult<'vir> {
    expr: vir::Expr<'vir>,

    /// Statements to undo the impure casts that were made to access the place.
    /// If the place was only accessed to take a snapshot or copy (rather than a
    /// move), these statements should be applied in-order to restore
    /// permissions to the root of the place.
    undo_casts: Vec<vir::Stmt<'vir>>,
}

impl<'vir> EncodePlaceResult<'vir> {
    fn new(expr: vir::Expr<'vir>) -> Self {
        Self { expr, undo_casts: Vec::new() }
    }

    fn map_expr(&mut self, f: impl FnOnce(vir::Expr<'vir>) -> vir::Expr<'vir>) -> &mut Self {
        self.expr = f(self.expr);
        self
    }
}

impl<'tcx, 'vir, 'enc> ImpureEncVisitor<'tcx, 'vir, 'enc> {
    fn stmt(&mut self, stmt: vir::Stmt<'vir>) {
        self.current_stmts
            .as_mut()
            .unwrap()
            .push(stmt);
    }

    fn unreachable(&mut self) -> vir::TerminatorStmt<'vir> {
        self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_bool::<false>()));
        self.vcx.mk_assume_false_stmt()
    }

    /*
    fn project_fields(
        &mut self,
        mut ty_out: crate::encoders::PredicateEncOutputRef<'vir>,
        projection: &'vir ty::List<mir::PlaceElem<'vir>>
    ) -> &'vir [&'vir str] {
        let mut ret = vec![];
        for proj in projection {
            match proj {
                mir::ProjectionElem::Field(f, ty) => {
                    let ty_out_struct = ty_out.expect_structlike();
                    let field_ty_out = self.deps.require_ref::<crate::encoders::PredicateEnc>(
                        ty,
                    ).unwrap();
                    ret.push();
                    ty_out = field_ty_out;
                }
                _ => panic!("unsupported projection"),
            }
        }
        ret
        self.vcx.alloc_slice(&projection.iter()
            .map(|proj| match proj {
            }).collect::<Vec<_>>())

        projection.iter()
            .fold((base, ty_out), |(base, ty_out), proj| match proj {
                mir::ProjectionElem::Field(f, ty) => {
                    let ty_out_struct = ty_out.expect_structlike();
                    let field_ty_out = self.deps.require_ref::<crate::encoders::PredicateEnc>(
                        ty,
                    ).unwrap();
                    (self.vcx.mk_func_app(
                        ty_out_struct.field_projection_p[f.as_usize()],
                        &[base],
                    ), field_ty_out)
                }
                _ => panic!("unsupported projection"),
            }).0
    }
    */

    /// Do the same as [self.fpcs_repacks_terminator] but instead of adding the statements to [self.current_stmts] return them instead.
    /// TODO: clean this up
    fn collect_terminator_repacks(
        &mut self,
        idx: usize,
        repacks: impl for<'a, 'b> Fn(&'a FreePcsLocation<'b>) -> &'a [RepackOp<'b>],
    ) -> Vec<&'vir vir::StmtData<'vir>> {
        let current_stmts = self.current_stmts.take();
        self.current_stmts = Some(Vec::new());
        self.fpcs_repacks_terminator(idx, repacks);
        let new_stmts = self.current_stmts.take().unwrap();
        self.current_stmts = current_stmts;
        new_stmts
    }

    fn fpcs_repacks(
        &mut self,
        repacks: &[RepackOp<'tcx>],
    ) {
        for &repack_op in repacks {
            match repack_op {
                RepackOp::Expand(place, _target, capability_kind)
                | RepackOp::Collapse(place, _target, capability_kind) => {
                    if matches!(capability_kind, CapabilityKind::Write) {
                        // Collapsing an already exhaled place is a no-op
                        // TODO: unless it's through a Ref I imagine?
                        assert!(matches!(repack_op, RepackOp::Collapse(..)));
                        return;
                    }
                    let place_ty = (*place).ty(self.local_decls, self.vcx.tcx());
                    let place_ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(place_ty.ty).unwrap();
                    let ref_to_pred = place_ty_out
                        .generic_predicate
                        .expect_pred_variant_opt(place_ty.variant_index);

                    let ref_p = self.encode_place(place).expr;
                    let args = place_ty_out.ref_to_args(self.vcx, ref_p);
                    let predicate = ref_to_pred.apply(self.vcx, &args, None);
                    if matches!(
                        repack_op,
                        mir_state_analysis::free_pcs::RepackOp::Expand(..)
                    ) {
                        self.stmt(self.vcx.mk_unfold_stmt(predicate));
                    } else {
                        self.stmt(self.vcx.mk_fold_stmt(predicate));
                    }
                }
                RepackOp::Weaken(place, CapabilityKind::Exclusive, CapabilityKind::Write) => {
                    let place_ty = (*place).ty(self.local_decls, self.vcx.tcx());
                    assert!(place_ty.variant_index.is_none());

                    let place_ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(place_ty.ty).unwrap();

                    let ref_p = self.encode_place(place).expr;
                    self.stmt(
                        self.vcx
                            .mk_exhale_stmt(place_ty_out.ref_to_pred(self.vcx, ref_p, None)),
                    );
                }
                unsupported_op => panic!("unsupported repack op: {unsupported_op:?}"),
            }
        }
    }

    fn fpcs_repacks_location(
        &mut self,
        location: mir::Location,
        repacks: impl for<'a, 'b> Fn(&'a FreePcsLocation<'b>) -> &'a [RepackOp<'b>],
    ) {
        let current_fpcs = self.current_fpcs.take().unwrap();
        let repacks = repacks(&current_fpcs.statements[location.statement_index]);
        self.fpcs_repacks(repacks);
        self.current_fpcs = Some(current_fpcs);
    }

    fn fpcs_repacks_terminator(
        &mut self,
        succ_idx: usize,
        repacks: impl for<'a, 'b> Fn(&'a FreePcsLocation<'b>) -> &'a [RepackOp<'b>],
    ) {
        let current_fpcs = self.current_fpcs.take().unwrap();
        let repacks = repacks(&current_fpcs.terminator.succs[succ_idx]);
        self.fpcs_repacks(repacks);
        self.current_fpcs = Some(current_fpcs);
    }

    fn undo_impure_casts(&mut self, result: EncodePlaceResult<'vir>) {
        result.undo_casts.iter().for_each(|stmt| self.stmt(stmt));
    }

    fn encode_operand_snap(&mut self, operand: &mir::Operand<'tcx>) -> vir::Expr<'vir> {
        let ty = operand.ty(self.local_decls, self.vcx.tcx());
        match operand {
            &mir::Operand::Move(source) => {
                let ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(ty).unwrap();
                let result = self.encode_place(Place::from(source));
                let snap_val = ty_out.ref_to_snap(self.vcx, result.expr);

                let tmp_exp = self.new_tmp(ty_out.snapshot()).1;
                self.stmt(self.vcx.mk_pure_assign_stmt(tmp_exp, snap_val));
                self.stmt(
                    self.vcx
                        .mk_exhale_stmt(ty_out.ref_to_pred(self.vcx, result.expr, None)),
                );
                tmp_exp
            }
            &mir::Operand::Copy(source) => {
                let ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(ty).unwrap();
                let result = self.encode_place(Place::from(source));
                let snap_val = ty_out.ref_to_snap(self.vcx, result.expr);
                let tmp_exp = self.new_tmp(ty_out.snapshot()).1;
                self.stmt(self.vcx.mk_pure_assign_stmt(tmp_exp, snap_val));
                self.undo_impure_casts(result);
                tmp_exp
            }
            mir::Operand::Constant(box constant) => self
                .deps
                .require_local::<ConstEnc>((constant.literal, 0, self.def_id))
                .unwrap(),
        }
    }

    fn encode_operand(
        &mut self,
        operand: &mir::Operand<'tcx>,
    ) -> vir::Expr<'vir> {
        let ty = operand.ty(self.local_decls, self.vcx.tcx());
        let (encode_place_result, ty_out) = match operand {
            &mir::Operand::Move(source) => return self.encode_place(Place::from(source)).expr,
            &mir::Operand::Copy(source) => {
                let ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(ty).unwrap();
                let mut result = self.encode_place(Place::from(source));
                result.map_expr(|e| ty_out.ref_to_snap(self.vcx, e));
                (result, ty_out)
            }
            mir::Operand::Constant(box constant) => {
                let ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(ty).unwrap();
                let constant = self.deps.require_local::<ConstEnc>((constant.literal, 0, self.def_id)).unwrap();
                (EncodePlaceResult::new(constant), ty_out)
            }
        };
        let tmp_exp: vir::Expr<'vir> = self.new_tmp(&vir::TypeData::Ref).1;
        self.stmt(ty_out.apply_method_assign(self.vcx, tmp_exp, encode_place_result.expr));
        self.undo_impure_casts(encode_place_result);
        tmp_exp
    }

    fn encode_place(
        &mut self,
        place: Place<'tcx>,
    ) -> EncodePlaceResult<'vir> {
        let mut place_ty = mir::tcx::PlaceTy::from_ty(self.local_decls[place.local].ty);
        let mut result = EncodePlaceResult::new(self.local_defs.locals[place.local].local_ex);
        // TODO: factor this out (duplication with pure encoder)?
        for &elem in place.projection {
            let (expr, unapply_cast_stmt) = self.encode_place_element(place_ty, elem, result.expr);
            result.expr = expr;
            if let Some(stmt) = unapply_cast_stmt {
                result.undo_casts.push(stmt);
            }
            place_ty = place_ty.projection_ty(self.vcx.tcx(), elem);
        }
        result
    }

    // Returns a tuple (expr, unapply_cast), where `expr` is the encoded place element,
    // and `unapply_cast` is a statement to undo the impure cast that was made to access
    // it.
    fn encode_place_element(
        &mut self,
        place_ty: mir::tcx::PlaceTy<'tcx>,
        elem: mir::PlaceElem<'tcx>,
        expr: vir::Expr<'vir>
    ) -> (vir::Expr<'vir>, Option<vir::Stmt<'vir>>) {
        match elem {
            mir::ProjectionElem::Field(field_idx, ty) => {
                let e_ty = self.deps.require_ref::<RustTyPredicatesEnc>(place_ty.ty).unwrap();
                let field_access = e_ty
                    .generic_predicate
                    .expect_variant_opt(place_ty.variant_index)
                    .ref_to_field_refs;
                let projection_p = field_access[field_idx.as_usize()];
                let proj_app = projection_p.apply(self.vcx, [expr]);
                let mut unapply_cast_stmt = None;
                match place_ty.ty.kind() {
                    TyKind::Adt(def, _) => {
                        let variant = def.variant(place_ty.variant_index.unwrap_or(
                            abi::FIRST_VARIANT
                        ));
                        let generic_field_ty = variant.fields[field_idx].ty(
                            self.vcx.tcx(),
                            GenericArgs::identity_for_item(self.vcx.tcx(), def.did())
                        );
                        let cast_args = CastArgs {
                            expected: ty,
                            actual: generic_field_ty
                        };
                        if let Some(cast) = self
                            .deps.require_ref::<CastToEnc<CastTypeImpure>>(cast_args)
                            .unwrap().apply_cast_if_necessary(self.vcx, proj_app) {
                                self.stmt(cast);
                                unapply_cast_stmt = self
                                    .deps
                                    .require_ref::<CastToEnc<CastTypeImpure>>(cast_args.reversed())
                                    .unwrap().apply_cast_if_necessary(self.vcx, proj_app);
                        }
                    }
                    TyKind::Tuple(_) => {
                        if let Some(cast_stmts) = self
                            .deps.require_local::<RustTyCastersEnc<CastTypeImpure>>(ty)
                            .unwrap().cast_to_concrete_if_possible(self.vcx, proj_app) {
                                self.stmt(cast_stmts.apply_cast_stmt);
                                unapply_cast_stmt = Some(cast_stmts.unapply_cast_stmt);
                        }
                    }
                    _ => {}
                }
                (proj_app, unapply_cast_stmt)
            }
            // TODO: should all variants start at the same `Ref`?
            mir::ProjectionElem::Downcast(..) => (expr, None),
            mir::ProjectionElem::Deref => {
                assert!(place_ty.variant_index.is_none());
                let e_ty = self.deps.require_ref::<RustTyPredicatesEnc>(place_ty.ty).unwrap();
                let ref_field = e_ty.generic_predicate.expect_ref().ref_field;
                let expr = self.vcx.mk_field_expr(expr, ref_field);
                let inner_ty = place_ty.ty.builtin_deref(true).unwrap().ty;
                if let Some(cast_stmts) = self
                    .deps.require_local::<RustTyCastersEnc<CastTypeImpure>>(inner_ty)
                    .unwrap().cast_to_concrete_if_possible(self.vcx, expr) {
                        self.stmt(cast_stmts.apply_cast_stmt);
                        return (expr, Some(cast_stmts.unapply_cast_stmt));
                }
                (expr, None)
            }
            _ => todo!("Unsupported ProjectionElem {:?}", elem),
        }
    }

    fn new_tmp(&mut self, ty: &'vir vir::TypeData<'vir>) -> (vir::Local<'vir>, vir::Expr<'vir>) {
        let name = vir::vir_format!(self.vcx, "_tmp{}", self.tmp_ctr);
        self.tmp_ctr += 1;
        self.stmt(self.vcx.mk_local_decl_stmt(
            vir::vir_local_decl! { self.vcx; [name] : [ty] },
            None,
        ));
        let tmp = self.vcx.mk_local(name, ty);
        (tmp, self.vcx.mk_local_ex_local(tmp))
    }
}

impl<'tcx, 'vir, 'enc> mir::visit::Visitor<'tcx> for ImpureEncVisitor<'tcx, 'vir, 'enc> {
    // fn visit_body(&mut self, body: &mir::Body<'tcx>) {
    //     println!("visiting body!");
    // }
    fn visit_basic_block_data(
        &mut self,
        block: mir::BasicBlock,
        data: &mir::BasicBlockData<'tcx>,
    ) {
        self.current_fpcs = Some(self.fpcs_analysis.get_all_for_bb(block));

        self.current_stmts = Some(Vec::with_capacity(
            data.statements.len(), // TODO: not exact?
        ));
        if ENCODE_REACH_BB {
            self.stmt(
                self.vcx.mk_pure_assign_stmt(
                    self.vcx.mk_local_ex(
                        vir::vir_format!(self.vcx, "_reach_bb{}", block.as_usize()),
                        &vir::TypeData::Bool,
                    ),
                    self.vcx.mk_bool::<true>()
                )
            );
        }

        /*
        let mut phi_stmts = vec![];
        if let Some(phi_nodes) = self.ssa_analysis.phi.get(&block) {
            for phi_node in phi_nodes {
                assert!(!phi_node.sources.is_empty());
                let local_ty = &self.local_types[phi_node.local];
                let expr = phi_node.sources.iter()
                    .fold(self.vcx.mk_func_app(
                        local_ty.function_unreachable,
                        &[],
                    ), |prev, source| self.vcx.alloc(vir::ExprData::Ternary(self.vcx.alloc(vir::TernaryData {
                        cond: self.vcx.mk_local_ex(vir::vir_format_identifier!(self.vcx, "_reach_bb{}", source.0.as_usize())),
                        then: self.vcx.mk_local_ex(vir::vir_format_identifier!(self.vcx, "_{}s_{}", phi_node.local.as_usize(), source.1)),
                        else_: prev,
                    }))));
                phi_stmts.push(vir::StmtData::LocalDecl(self.vcx.alloc(vir::LocalDeclData {
                    name: vir::vir_format_identifier!(self.vcx, "_{}s_{}", phi_node.local.as_usize(), phi_node.new_version),
                    ty: self.local_types[phi_node.local].snapshot,
                    expr: Some(expr),
                })));
            }
        }
        for phi_stmt in phi_stmts {
            self.stmt(phi_stmt);
        }
        */

        assert!(self.current_terminator.is_none());
        self.super_basic_block_data(block, data);
        let stmts = self.current_stmts.take().unwrap();
        let terminator = self.current_terminator.take().unwrap();
        self.encoded_blocks.push(
            self.vcx.mk_cfg_block(
                self.vcx.alloc(vir::CfgBlockLabelData::BasicBlock(block.as_usize())),
                self.vcx.alloc_slice(&stmts),
                terminator
            )
        );
    }

    fn visit_statement(
        &mut self,
        statement: &mir::Statement<'tcx>,
        location: mir::Location,
    ) {
        // TODO: these should not be ignored, but should havoc the local instead
        // This clears up the noise a bit, making sure StorageLive and other
        // kinds do not show up in the comments.
        let IGNORE_NOP_STMTS = true;
        if IGNORE_NOP_STMTS {
            match &statement.kind {
                mir::StatementKind::StorageLive(..)
                | mir::StatementKind::StorageDead(..) => {
                    return;
                }
                _ => {}
            }
        }

        self.stmt(self.vcx.mk_comment_stmt(
            // TODO: also add bb and location for better debugging?
            vir::vir_format!(self.vcx, "{statement:?}"),
        ));

        self.fpcs_repacks_location(location, |loc| &loc.repacks_start);
        // TODO: move this to after getting operands, before assignment
        self.fpcs_repacks_location(location, |loc| &loc.repacks_middle);
        match &statement.kind {
            mir::StatementKind::Assign(box (dest, rvalue)) => {
                //let ssa_update = self.ssa_analysis.updates.get(&location).cloned().unwrap();
                //assert!(ssa_update.local == dest.local);

                //let old_name_s = vir::vir_format_identifier!(self.vcx, "_{}s_{}", dest.local.index(), ssa_update.old_version);
                //let name_s = vir::vir_format_identifier!(self.vcx, "_{}s_{}", dest.local.index(), ssa_update.new_version);
                //let ty_s = self.local_types[ssa_update.local].snapshot;

                // What are we assigning to?
                let proj_ref = self.encode_place(Place::from(*dest)).expr;

                let rvalue_ty = rvalue.ty(self.local_decls, self.vcx.tcx());

                // The snapshot of the value that we are assigning.
                let expr = match rvalue {
                    mir::Rvalue::Use(op) => self.encode_operand_snap(op),

                    //mir::Rvalue::Repeat(Operand<'tcx>, Const<'tcx>) => {}
                    //mir::Rvalue::Ref(Region<'tcx>, BorrowKind, Place<'tcx>) => {}
                    //mir::Rvalue::ThreadLocalRef(DefId) => {}
                    //mir::Rvalue::AddressOf(Mutability, Place<'tcx>) => {}
                    //mir::Rvalue::Len(Place<'tcx>) => {}
                    //mir::Rvalue::Cast(CastKind, Operand<'tcx>, Ty<'tcx>) => {}

                    rv@mir::Rvalue::BinaryOp(op, box (l, r)) |
                    rv@mir::Rvalue::CheckedBinaryOp(op, box (l, r)) => {
                        let l_ty = l.ty(self.local_decls, self.vcx.tcx());
                        let r_ty = r.ty(self.local_decls, self.vcx.tcx());
                        use crate::encoders::MirBuiltinEncTask::{BinOp, CheckedBinOp};
                        let task = if matches!(rv, mir::Rvalue::BinaryOp(..)) {
                            BinOp(rvalue_ty, *op, l_ty, r_ty)
                        } else {
                            CheckedBinOp(rvalue_ty, *op, l_ty, r_ty)
                        };
                        let binop_function = self.deps.require_ref::<MirBuiltinEnc>(
                            task
                        ).unwrap().function;
                        binop_function.apply(self.vcx, &[
                            self.encode_operand_snap(l),
                            self.encode_operand_snap(r),
                        ])
                    }

                    //mir::Rvalue::NullaryOp(NullOp, Ty<'tcx>) => {}

                    mir::Rvalue::UnaryOp(unop, operand) => {
                        let operand_ty = operand.ty(self.local_decls, self.vcx.tcx());
                        let unop_function = self.deps.require_ref::<MirBuiltinEnc>(
                            crate::encoders::MirBuiltinEncTask::UnOp(
                                rvalue_ty,
                                *unop,
                                operand_ty,
                            ),
                        ).unwrap().function;
                        unop_function.apply(self.vcx, &[self.encode_operand_snap(operand)])
                        /*
                        assert!(source.projection.is_empty());
                        let source_version = self.ssa_analysis.version.get(&(location, source.local)).unwrap();
                        let source_name = vir::vir_format_identifier!(self.vcx, "_{}s_{}", source.local.index(), source_version);

                        let unop_function = self.deps.require_ref::<crate::encoders::MirBuiltinEnc>(
                            crate::encoders::MirBuiltinEncTask::UnOp(
                                *unop,
                                source.ty(self.local_decls, self.vcx.tcx()).ty,
                            ),
                        ).unwrap().name;
                        Some(self.vcx.mk_func_app(
                            unop_function,
                            &[self.vcx.mk_local_ex(source_name)],
                        ))*/
                    }

                    mir::Rvalue::Aggregate(
                        box kind @ (mir::AggregateKind::Adt(..) | mir::AggregateKind::Tuple),
                        fields,
                    ) => {
                        let e_rvalue_ty = self.deps.require_ref::<RustTyPredicatesEnc>(rvalue_ty).unwrap();
                        let sl = match kind {
                            mir::AggregateKind::Adt(_, vidx, _, _, _) =>
                                e_rvalue_ty.generic_predicate.get_variant_any(*vidx),
                            _ => e_rvalue_ty.generic_predicate.expect_structlike()
                        };
                        let field_tys = fields.iter()
                            .map(|field| field.ty(self.local_decls, self.vcx.tcx()))
                            .collect::<Vec<_>>();
                        let ty_caster = self.deps.require_local::<AggregateSnapArgsCastEnc>(
                            AggregateSnapArgsCastEncTask {
                                tys: field_tys,
                                aggregate_type: kind.into()
                            }
                        ).unwrap();
                        let field_snaps = fields.iter().map(|field| self.encode_operand_snap(field)).collect::<Vec<_>>();
                        let casted_args = ty_caster.apply_casts(self.vcx, field_snaps.into_iter());
                        sl.snap_data.field_snaps_to_snap.apply(self.vcx, self.vcx.alloc_slice(&casted_args))
                    }
                    mir::Rvalue::Discriminant(place) => {
                        let e_rvalue_ty = self.deps.require_ref::<RustTyPredicatesEnc>(rvalue_ty).unwrap();
                        let place_ty = place.ty(self.local_decls, self.vcx.tcx());
                        let ty = self.deps.require_ref::<RustTyPredicatesEnc>(place_ty.ty).unwrap();
                        let place_expr = self.encode_place(Place::from(*place)).expr;

                        match ty.generic_predicate.get_enumlike().filter(|_| place_ty.variant_index.is_none()) {
                            Some(el) => {
                                let discr_expr = self.vcx.mk_field_expr(place_expr, el.as_ref().unwrap().discr);
                                self.vcx.mk_unfolding_expr(ty.ref_to_pred_app(self.vcx, place_expr, Some(self.vcx.mk_wildcard())), discr_expr)
                            }
                            None => {
                                // mir::Rvalue::Discriminant documents "Returns zero for types without discriminant"
                                let zero = self.vcx.mk_uint::<0>();
                                e_rvalue_ty.generic_predicate.expect_prim().prim_to_snap.apply(self.vcx, [zero])
                            }
                        }
                    }

                    //mir::Rvalue::Discriminant(Place<'tcx>) => {}
                    //mir::Rvalue::ShallowInitBox(Operand<'tcx>, Ty<'tcx>) => {}
                    //mir::Rvalue::CopyForDeref(Place<'tcx>) => {}
                    other => {
                        tracing::error!("unsupported rvalue {other:?}");
                        self.vcx.mk_todo_expr(vir::vir_format!(self.vcx, "rvalue {rvalue:?}"))
                    }
                };

                let dest_ty = dest.ty(self.local_decls, self.vcx.tcx());
                assert!(dest_ty.variant_index.is_none());
                let dest_ty_out = self.deps.require_ref::<RustTyPredicatesEnc>(dest_ty.ty).unwrap();
                let method_assign_app = dest_ty_out.apply_method_assign(
                    self.vcx,
                    proj_ref,
                    expr
                );

                self.stmt(method_assign_app);
            }

            // no-ops ?
            mir::StatementKind::StorageLive(..)
            | mir::StatementKind::StorageDead(..) => {}

            // no-ops
            mir::StatementKind::FakeRead(_)
            | mir::StatementKind::Retag(..)
            | mir::StatementKind::PlaceMention(_)
            | mir::StatementKind::AscribeUserType(..)
            | mir::StatementKind::Coverage(_)
            //| mir::StatementKind::ConstEvalCounter
            | mir::StatementKind::Nop => {}

            k => todo!("statement {k:?}"),
        }
    }

    fn visit_terminator(
        &mut self,
        terminator: &mir::Terminator<'tcx>,
        location: mir::Location,
    ) {
        self.stmt(self.vcx.mk_comment_stmt(
            // TODO: also add bb and location for better debugging?
            vir::vir_format!(self.vcx, "{:?}", terminator.kind),
        ));

        self.fpcs_repacks_location(location, |loc| &loc.repacks_start);
        // TODO: move this to after getting operands, before assignment
        self.fpcs_repacks_location(location, |loc| &loc.repacks_middle);
        let terminator = match &terminator.kind {
            mir::TerminatorKind::Goto { target }
            | mir::TerminatorKind::FalseUnwind { real_target: target, .. }
            | mir::TerminatorKind::FalseEdge { real_target: target, .. }  => {
                const REAL_TARGET_SUCC_IDX: usize = 0;
                // Ensure that the terminator succ that we use for the repacks is the correct one
                assert_eq!(&self.current_fpcs.as_ref().unwrap().terminator.succs[REAL_TARGET_SUCC_IDX].location.block, target);
                self.fpcs_repacks_terminator(REAL_TARGET_SUCC_IDX, |rep| &rep.repacks_start);

                self.vcx.mk_goto_stmt(
                    self.vcx
                        .alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize())),
                )
            }
            mir::TerminatorKind::SwitchInt { discr, targets } => {
                //let discr_version = self.ssa_analysis.version.get(&(location, discr.local)).unwrap();
                //let discr_name = vir::vir_format_identifier!(self.vcx, "_{}s_{}", discr.local.index(), discr_version);
                let discr_ty_rs = discr.ty(self.local_decls, self.vcx.tcx());
                let discr_ty = self
                    .deps
                    .require_ref::<RustTyPredicatesEnc>(discr_ty_rs)
                    .unwrap()
                    .generic_predicate
                    .expect_prim();

                let goto_targets = self.vcx.alloc_slice(
                    &targets
                        .iter()
                        .enumerate()
                        .map(|(idx, (value, target))| {
                            assert_eq!(
                                self.current_fpcs.as_ref().unwrap().terminator.succs[idx]
                                    .location
                                    .block,
                                target
                            );

                        let extra_stmts = self.collect_terminator_repacks(idx, |rep| &rep.repacks_start);
                        self.vcx.mk_goto_if_target(
                            discr_ty.expr_from_bits(discr_ty_rs, value),
                            self.vcx.alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize())),
                            self.vcx.alloc_slice(&extra_stmts),
                        )
                    })
                    .collect::<Vec<_>>());
                let goto_otherwise = self.vcx.alloc(vir::CfgBlockLabelData::BasicBlock(
                    targets.otherwise().as_usize(),
                ));

                let otherwise_succ_idx = goto_targets.len();
                assert_eq!(self.current_fpcs.as_ref().unwrap().terminator.succs[otherwise_succ_idx].location.block, targets.otherwise());
                let otherwise_stmts = self.collect_terminator_repacks(otherwise_succ_idx, |rep| &rep.repacks_start);

                let discr_ex = discr_ty.snap_to_prim.apply(self.vcx, [self.encode_operand_snap(discr)]);
                self.vcx.mk_goto_if_stmt(
                    discr_ex, // self.vcx.mk_local_ex(discr_name),
                    goto_targets,
                    goto_otherwise,
                    self.vcx.alloc_slice(&otherwise_stmts),
                )
            }
            mir::TerminatorKind::Return =>
                self.vcx.mk_goto_stmt(self.vcx.alloc(vir::CfgBlockLabelData::End)),
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => {
                let (func_def_id, caller_substs) = self.get_def_id_and_caller_substs(func);
                let is_pure = crate::encoders::with_proc_spec(func_def_id, |spec|
                    spec.kind.is_pure().unwrap_or_default()
                ).unwrap_or_default();

                let dest = self.encode_place(Place::from(*destination)).expr;

                let task = (func_def_id, self.def_id);
                let sig = self.vcx().tcx().fn_sig(func_def_id);
                let sig = if self.monomorphize {
                    let param_env = self.vcx().tcx().param_env(self.def_id);
                    self.vcx().tcx().subst_and_normalize_erasing_regions(
                        caller_substs,
                        param_env,
                        sig
                    )
                } else {
                    sig.instantiate_identity()
                };
                let fn_arg_tys = sig
                    .inputs()
                    .iter()
                    .map(|i| i.skip_binder())
                    .copied()
                    .collect::<Vec<_>>();
                if is_pure {
                    let pure_func_app = self.encode_pure_func_app(
                        func_def_id,
                        sig,
                        caller_substs,
                        args,
                        destination,
                        self.def_id,
                        &()
                    );

                    let return_ty = destination.ty(self.local_decls, self.vcx.tcx()).ty;
                    let assign_stmt = self
                        .deps
                        .require_ref::<RustTyPredicatesEnc>(return_ty)
                        .unwrap()
                        .apply_method_assign(self.vcx, dest, pure_func_app);

                    self.stmt(assign_stmt);
                } else {
                    let func_out = self
                        .deps
                        .require_ref::<encoders::MirImpureEnc>(
                            FunctionCallTaskDescription::new(
                                task.0, caller_substs, task.1
                            )
                        )
                        .unwrap();


                    let method_in = args.iter().map(|arg| self.encode_operand(arg)).collect::<Vec<_>>();


                   for ((fn_arg_ty, arg), arg_ex) in fn_arg_tys.iter().zip(args.iter()).zip(method_in.iter()) {
                        let local_decls = self.local_decls_src();
                        let tcx = self.vcx().tcx();
                        let arg_ty = arg.ty(local_decls, tcx);
                        let caster = self.deps()
                            .require_ref::<CastToEnc<CastTypeImpure>>(CastArgs {
                                expected: *fn_arg_ty,
                                actual: arg_ty
                            })
                            .unwrap();
                        // In this context, `apply_cast_if_necessary` returns
                        // the impure operation to perform the cast
                        if let Some(stmt) = caster.apply_cast_if_necessary(self.vcx(), arg_ex) {
                            self.stmt(stmt);
                        }
                    }

                    let mut method_args =
                        std::iter::once(dest).chain(method_in).collect::<Vec<_>>();
                    let mono = self.monomorphize;
                    let encoded_ty_args = self
                        .deps()
                        .require_local::<LiftedFuncAppTyParamsEnc>(
                            (mono, caller_substs)
                        )
                        .unwrap()
                        .iter()
                        .map(|ty| ty.expr(self.vcx()));

                    method_args.extend(encoded_ty_args);

                    self.stmt(
                        self.vcx
                            .alloc(func_out.method_ref.apply(self.vcx, &method_args)),
                    );
                    let expected_ty = destination.ty(self.local_decls_src(), self.vcx.tcx()).ty;
                    let fn_result_ty = sig.output().skip_binder();
                    let result_cast = self
                        .deps()
                        .require_ref::<CastToEnc<CastTypeImpure>>(CastArgs {
                            expected: expected_ty,
                            actual: fn_result_ty,
                        })
                        .unwrap();
                    if let Some(stmt) = result_cast.apply_cast_if_necessary(self.vcx, dest) {
                        self.stmt(stmt);
                    }
                }

                target
                    .map(|target| {
                        self.vcx.mk_goto_stmt(
                            self.vcx
                                .alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize())),
                        )
                    })
                    .unwrap_or_else(|| self.unreachable())
            }
            mir::TerminatorKind::Assert {
                cond,
                expected,
                target,
                unwind,
                ..
            } => {
                let e_bool = self
                    .deps
                    .require_ref::<RustTyPredicatesEnc>(self.vcx.tcx().types.bool)
                    .unwrap();
                let enc = self.encode_operand_snap(cond);
                let enc = e_bool
                    .generic_predicate
                    .expect_prim()
                    .snap_to_prim
                    .apply(self.vcx, [enc]);
                let expected = self.vcx.mk_const_expr(vir::ConstData::Bool(*expected));
                let assert = self
                    .vcx
                    .mk_bin_op_expr(vir::BinOpKind::CmpEq, enc, expected);
                self.stmt(self.vcx.mk_exhale_stmt(assert));

                let target_bb = self
                    .vcx
                    .alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize()));
                let otherwise = match unwind {
                    mir::UnwindAction::Cleanup(bb) => self
                        .vcx
                        .alloc(vir::CfgBlockLabelData::BasicBlock(bb.as_usize())),
                    _ => todo!(),
                };

                self.vcx.mk_goto_if_stmt(enc, self.vcx.alloc_slice(&[self.vcx.mk_goto_if_target(
                    expected,
                    target_bb,
                    &[],
                )]), otherwise, &[])
            }
            mir::TerminatorKind::Unreachable => self.unreachable(),

            mir::TerminatorKind::Drop { target, .. } => {
                self.vcx.mk_goto_stmt(
                    self.vcx
                        .alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize())),
                )
            }

            unsupported_kind => self.vcx.mk_dummy_stmt(
                vir::vir_format!(self.vcx, "terminator {unsupported_kind:?}")
            ),
        };
        assert!(self.current_terminator.replace(terminator).is_none());
    }
}
