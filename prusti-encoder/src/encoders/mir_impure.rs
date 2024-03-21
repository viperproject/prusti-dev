use prusti_rustc_interface::{
    middle::{mir, ty},
    span::def_id::DefId,
};
use mir_state_analysis::{
    free_pcs::{FreePcsAnalysis, FreePcsBasicBlock, FreePcsLocation, RepackOp, CapabilityKind}, utils::Place,
};
//use mir_ssa_analysis::{
//    SsaAnalysis,
//};
use task_encoder::{
    TaskEncoder,
    TaskEncoderDependencies,
};
use vir::{MethodIdent, UnknownArity, CallableIdent};

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

use crate::encoders::{PredicateEnc, ConstEnc, MirBuiltinEnc, MirFunctionEnc, MirLocalDefEnc, MirSpecEnc};

const ENCODE_REACH_BB: bool = false;

impl TaskEncoder for MirImpureEnc {
    task_encoder::encoder_cache!(MirImpureEnc);

    // TODO: local def id (+ promoted, substs, etc)
    type TaskDescription<'tcx> = (
        DefId, // ID of the function
        ty::GenericArgsRef<'tcx>, // ? this should be the "signature", after applying the env/substs
        Option<DefId>, // ID of the caller function, if any
    );

    type OutputRef<'vir> = MirImpureEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = MirImpureEncOutput<'vir>;

    type EncodingError = MirImpureEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'tcx: 'vir, 'vir>(
        task_key: &Self::TaskKey<'tcx>,
        deps: &mut TaskEncoderDependencies<'vir>,
    ) -> Result<(
        Self::OutputFullLocal<'vir>,
        Self::OutputFullDependency<'vir>,
    ), (
        Self::EncodingError,
        Option<Self::OutputFullDependency<'vir>>,
    )> {
        let (def_id, substs, caller_def_id) = *task_key;

        let trusted = crate::encoders::with_proc_spec(def_id, |def_spec|
            def_spec.trusted.extract_inherit().unwrap_or_default()
        ).unwrap_or_default();

        vir::with_vcx(|vcx| {
            use mir::visit::Visitor;
            let local_defs = deps.require_local::<MirLocalDefEnc>(
                *task_key,
            ).unwrap();

            // Argument count for the Viper method:
            // - one (`Ref`) for the return place;
            // - one (`Ref`) for each MIR argument.
            //
            // Note that the return place is modelled as an argument of the
            // Viper method. This corresponds to an execution model where the
            // method can return data to the caller without a copy--it directly
            // modifies a place provided by the caller.
            //
            // TODO: type parameters
            let arg_count = local_defs.arg_count + 1;

            let extra: String = substs.iter().map(|s| format!("_{s}")).collect();
            let caller = caller_def_id.map(|id| format!("{}_{}", id.krate, id.index.index())).unwrap_or_default();
            let method_name = vir::vir_format!(vcx, "m_{}{extra}_CALLER_{caller}", vcx.tcx().item_name(def_id));
            let args = vec![&vir::TypeData::Ref; arg_count];
            let args = UnknownArity::new(vcx.alloc_slice(&args));
            let method_ref = MethodIdent::new(method_name, args);
            deps.emit_output_ref::<Self>(*task_key, MirImpureEncOutputRef {
                method_ref,
            });

            // Do not encode the method body if it is external, trusted or just
            // a call stub.
            let local_def_id = def_id.as_local().filter(|_| !trusted && caller_def_id.is_none());
            let blocks = if let Some(local_def_id) = local_def_id {
                let body = vcx.body_mut().get_impure_fn_body(local_def_id, substs, caller_def_id);
                // let body = vcx.tcx().mir_promoted(local_def_id).0.borrow();

                let fpcs_analysis = mir_state_analysis::run_free_pcs(&body, vcx.tcx());

                //let ssa_analysis = SsaAnalysis::analyse(&body);

                let block_count = body.basic_blocks.len();

                // Local count for the Viper method:
                // - one for each basic block;
                // - one (`Ref`) for each non-argument, non-return local.
                let _local_count = block_count + 1 * (body.local_decls.len() - arg_count);

                let mut encoded_blocks = Vec::with_capacity(
                    // extra blocks: Start, End
                    2 + block_count,
                );
                let mut start_stmts = Vec::new();
                for local in (arg_count..body.local_decls.len()).map(mir::Local::from) {
                    let name_p = local_defs.locals[local].local.name;
                    start_stmts.push(
                        vcx.mk_local_decl_stmt(vir::vir_local_decl! { vcx; [name_p] : Ref }, None)
                    )
                }
                if ENCODE_REACH_BB {
                    start_stmts.extend((0..block_count)
                        .map(|block| {
                            let name = vir::vir_format!(vcx, "_reach_bb{block}");
                            vcx.mk_local_decl_stmt(
                                vir::vir_local_decl! { vcx; [name] : Bool },
                                Some(vcx.mk_todo_expr("false"))
                            )
                        }));
                }
                encoded_blocks.push(
                    vcx.mk_cfg_block(
                        vcx.alloc(vir::CfgBlockLabelData::Start),
                        vcx.alloc_slice(&start_stmts),
                        vcx.mk_goto_stmt(vcx.alloc(vir::CfgBlockLabelData::BasicBlock(0)))
                    )
                );

                let mut visitor = EncVisitor {
                    vcx,
                    deps,
                    def_id,
                    local_decls: &body.local_decls,
                    //ssa_analysis,
                    fpcs_analysis,
                    local_defs,

                    tmp_ctr: 0,

                    current_fpcs: None,

                    current_stmts: None,
                    current_terminator: None,
                    encoded_blocks,
                };
                visitor.visit_body(&body);

                visitor.encoded_blocks.push(
                    vcx.mk_cfg_block(
                        vcx.alloc(vir::CfgBlockLabelData::End),
                        &[],
                        vcx.alloc(vir::TerminatorStmtData::Exit)
                    )
                );
                Some(vcx.alloc_slice(&visitor.encoded_blocks))
            } else {
                None
            };

            let spec = deps.require_local::<MirSpecEnc>(
                (def_id, substs, caller_def_id, false)
            ).unwrap();
            let (spec_pres, spec_posts) = (spec.pres, spec.posts);

            let mut pres = Vec::with_capacity(arg_count - 1);
            let mut args = Vec::with_capacity(arg_count);
            for arg_idx in 0..arg_count {
                let name_p = local_defs.locals[arg_idx.into()].local.name;
                args.push(vir::vir_local_decl! { vcx; [name_p] : Ref });
                if arg_idx != 0 {
                    pres.push(local_defs.locals[arg_idx.into()].impure_pred);
                }
            }
            pres.extend(spec_pres);

            let mut posts = Vec::with_capacity(spec_posts.len() + 1);
            posts.push(local_defs.locals[mir::RETURN_PLACE].impure_pred);
            posts.extend(spec_posts);

            Ok((MirImpureEncOutput {
                method: vcx.mk_method(
                    method_name,
                    vcx.alloc_slice(&args),
                    &[],
                    vcx.alloc_slice(&pres),
                    vcx.alloc_slice(&posts),
                    blocks
                ),
            }, ()))
        })
    }
}

struct EncVisitor<'tcx, 'vir, 'enc>
    where 'vir: 'enc
{
    vcx: &'vir vir::VirCtxt<'tcx>,
    deps: &'enc mut TaskEncoderDependencies<'vir>,
    def_id: DefId,
    local_decls: &'enc mir::LocalDecls<'tcx>,
    //ssa_analysis: SsaAnalysis,
    fpcs_analysis: FreePcsAnalysis<'enc, 'tcx>,
    local_defs: crate::encoders::local_def::MirLocalDefEncOutput<'vir>,

    tmp_ctr: usize,

    // for the current basic block
    current_fpcs: Option<FreePcsBasicBlock<'tcx>>,

    current_stmts: Option<Vec<vir::Stmt<'vir>>>,
    current_terminator: Option<vir::TerminatorStmt<'vir>>,

    encoded_blocks: Vec<vir::CfgBlock<'vir>>, // TODO: use IndexVec ?
}

impl<'tcx, 'vir, 'enc> EncVisitor<'tcx, 'vir, 'enc> {
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
                    let place_ty_out = self.deps.require_ref::<PredicateEnc>(place_ty.ty).unwrap();
                    let ref_to_pred = place_ty_out.expect_pred_variant_opt(place_ty.variant_index);

                    let ref_p = self.encode_place(place);
                    let predicate = ref_to_pred.apply(self.vcx, [ref_p], None);
                    if matches!(repack_op, mir_state_analysis::free_pcs::RepackOp::Expand(..)) {
                        self.stmt(self.vcx.mk_unfold_stmt(predicate));
                    } else {
                        self.stmt(self.vcx.mk_fold_stmt(predicate));
                    }
                }
                RepackOp::Weaken(place, CapabilityKind::Exclusive, CapabilityKind::Write) => {
                    let place_ty = (*place).ty(self.local_decls, self.vcx.tcx());
                    assert!(place_ty.variant_index.is_none());

                    let place_ty_out = self.deps.require_ref::<PredicateEnc>(place_ty.ty).unwrap();

                    let ref_p = self.encode_place(place);
                    self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_predicate_app_expr(
                        place_ty_out.ref_to_pred.apply(self.vcx, [ref_p], None)
                    )));
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

    fn encode_operand_snap(
        &mut self,
        operand: &mir::Operand<'tcx>,
    ) -> vir::Expr<'vir> {
        let ty = operand.ty(self.local_decls, self.vcx.tcx());
        match operand {
            &mir::Operand::Move(source) => {
                let ty_out = self.deps.require_ref::<PredicateEnc>(ty).unwrap();
                let place_exp = self.encode_place(Place::from(source));
                let snap_val = ty_out.ref_to_snap.apply(self.vcx, [place_exp]);

                let tmp_exp = self.new_tmp(ty_out.snapshot).1;
                self.stmt(self.vcx.mk_pure_assign_stmt(tmp_exp, snap_val));
                self.stmt(self.vcx.mk_exhale_stmt(self.vcx.mk_predicate_app_expr(
                    ty_out.ref_to_pred.apply(self.vcx, [place_exp], None)
                )));
                tmp_exp
            }
            &mir::Operand::Copy(source) => {
                let ty_out = self.deps.require_ref::<PredicateEnc>(ty).unwrap();
                ty_out.ref_to_snap.apply(self.vcx, [self.encode_place(Place::from(source))])
            }
            mir::Operand::Constant(box constant) =>
                self.deps.require_local::<ConstEnc>((constant.literal, 0, self.def_id)).unwrap()
        }
    }

    fn encode_operand(
        &mut self,
        operand: &mir::Operand<'tcx>,
    ) -> vir::Expr<'vir> {
        let ty = operand.ty(self.local_decls, self.vcx.tcx());
        let (snap_val, ty_out) = match operand {
            &mir::Operand::Move(source) => return self.encode_place(Place::from(source)),
            &mir::Operand::Copy(source) => {
                let ty_out = self.deps.require_ref::<PredicateEnc>(ty).unwrap();
                let source = ty_out.ref_to_snap.apply(self.vcx, [self.encode_place(Place::from(source))]);
                (source, ty_out)
            }
            mir::Operand::Constant(box constant) => {
                let ty_out = self.deps.require_ref::<PredicateEnc>(ty).unwrap();
                let constant = self.deps.require_local::<ConstEnc>((constant.literal, 0, self.def_id)).unwrap();
                (constant, ty_out)
            }
        };
        let tmp_exp = self.new_tmp(&vir::TypeData::Ref).1;
        self.stmt(self.vcx.alloc(ty_out.method_assign.apply(self.vcx, [tmp_exp, snap_val])));
        tmp_exp
    }

    fn encode_place(
        &mut self,
        place: Place<'tcx>,
    ) -> vir::Expr<'vir> {
        let mut place_ty = mir::tcx::PlaceTy::from_ty(self.local_decls[place.local].ty);
        let mut expr = self.local_defs.locals[place.local].local_ex;
        // TODO: factor this out (duplication with pure encoder)?
        for &elem in place.projection {
            expr = self.encode_place_element(place_ty, elem, expr);
            place_ty = place_ty.projection_ty(self.vcx.tcx(), elem);
        }
        expr
    }

    fn encode_place_element(&mut self, place_ty: mir::tcx::PlaceTy<'tcx>, elem: mir::PlaceElem<'tcx>, expr: vir::Expr<'vir>) -> vir::Expr<'vir> {
        match elem {
            mir::ProjectionElem::Field(field_idx, _) => {
                let e_ty = self.deps.require_ref::<PredicateEnc>(place_ty.ty).unwrap();
                let field_access = e_ty.expect_variant_opt(place_ty.variant_index).ref_to_field_refs;
                let projection_p = field_access[field_idx.as_usize()];
                projection_p.apply(self.vcx, [expr])
            }
            // TODO: should all variants start at the same `Ref`?
            mir::ProjectionElem::Downcast(..) => expr,
            mir::ProjectionElem::Deref => {
                assert!(place_ty.variant_index.is_none());
                let e_ty = self.deps.require_ref::<PredicateEnc>(place_ty.ty).unwrap();
                let ref_field = e_ty.expect_ref().ref_field;
                self.vcx.mk_field_expr(expr, ref_field)
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

impl<'tcx, 'vir, 'enc> mir::visit::Visitor<'tcx> for EncVisitor<'tcx, 'vir, 'enc> {
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
                        cond: self.vcx.mk_local_ex(vir::vir_format!(self.vcx, "_reach_bb{}", source.0.as_usize())),
                        then: self.vcx.mk_local_ex(vir::vir_format!(self.vcx, "_{}s_{}", phi_node.local.as_usize(), source.1)),
                        else_: prev,
                    }))));
                phi_stmts.push(vir::StmtData::LocalDecl(self.vcx.alloc(vir::LocalDeclData {
                    name: vir::vir_format!(self.vcx, "_{}s_{}", phi_node.local.as_usize(), phi_node.new_version),
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

                //let old_name_s = vir::vir_format!(self.vcx, "_{}s_{}", dest.local.index(), ssa_update.old_version);
                //let name_s = vir::vir_format!(self.vcx, "_{}s_{}", dest.local.index(), ssa_update.new_version);
                //let ty_s = self.local_types[ssa_update.local].snapshot;

                // What are we assigning to?
                let proj_ref = self.encode_place(Place::from(*dest));

                let rvalue_ty = rvalue.ty(self.local_decls, self.vcx.tcx());
                let e_rvalue_ty = self.deps.require_ref::<PredicateEnc>(
                    rvalue_ty,
                ).unwrap();

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
                        let source_name = vir::vir_format!(self.vcx, "_{}s_{}", source.local.index(), source_version);

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
                        let sl = match kind {
                            mir::AggregateKind::Adt(_, vidx, _, _, _) =>
                                e_rvalue_ty.get_variant_any(*vidx),
                            _ => e_rvalue_ty.expect_structlike()
                        };
                        let cons_args: Vec<_> = fields.iter().map(|field| self.encode_operand_snap(field)).collect();
                        sl.snap_data.field_snaps_to_snap.apply(self.vcx, &cons_args)
                    }
                    mir::Rvalue::Discriminant(place) => {
                        let place_ty = place.ty(self.local_decls, self.vcx.tcx());
                        let ty = self.deps.require_ref::<PredicateEnc>(place_ty.ty).unwrap();
                        let place_expr = self.encode_place(Place::from(*place));

                        match ty.get_enumlike().filter(|_| place_ty.variant_index.is_none()) {
                            Some(el) => {
                                let discr_expr = self.vcx.mk_field_expr(place_expr, el.as_ref().unwrap().discr);
                                self.vcx.mk_unfolding_expr(ty.ref_to_pred.apply(self.vcx, [place_expr], Some(self.vcx.mk_wildcard())), discr_expr)
                            }
                            None => {
                                // mir::Rvalue::Discriminant documents "Returns zero for types without discriminant"
                                let zero = self.vcx.mk_uint::<0>();
                                e_rvalue_ty.expect_prim().prim_to_snap.apply(self.vcx, [zero])
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
                let dest_ty_out = self.deps.require_ref::<PredicateEnc>(dest_ty.ty,).unwrap();

                self.stmt(self.vcx.alloc(dest_ty_out.method_assign.apply(self.vcx, [proj_ref, expr])));
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
                    self.vcx.alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize()))
                )
            }
            mir::TerminatorKind::SwitchInt { discr, targets } => {
                //let discr_version = self.ssa_analysis.version.get(&(location, discr.local)).unwrap();
                //let discr_name = vir::vir_format!(self.vcx, "_{}s_{}", discr.local.index(), discr_version);
                let discr_ty_rs = discr.ty(self.local_decls, self.vcx.tcx());
                let discr_ty = self.deps.require_ref::<PredicateEnc>(
                    discr_ty_rs
                ).unwrap().expect_prim();

                let goto_targets = self.vcx.alloc_slice(&targets.iter().enumerate()
                    .map(|(idx, (value, target))| {
                        assert_eq!(self.current_fpcs.as_ref().unwrap().terminator.succs[idx].location.block, target);

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
                // TODO: extracting FnDef given func could be extracted? (duplication in pure)
                let func_ty = func.ty(self.local_decls, self.vcx.tcx());
                let (func_def_id, arg_tys) = match func_ty.kind() {
                    &ty::TyKind::FnDef(def_id, arg_tys) => {
                        (def_id, arg_tys)
                    }
                    _ => todo!(),
                };
                let is_pure = crate::encoders::with_proc_spec(func_def_id, |spec|
                    spec.kind.is_pure().unwrap_or_default()
                ).unwrap_or_default();

                let dest = self.encode_place(Place::from(*destination));

                let task = (func_def_id, arg_tys, self.def_id);
                if is_pure {
                    let pure_func = self.deps.require_ref::<MirFunctionEnc>(
                        task
                    ).unwrap();

                    let func_args: Vec<_> = args.iter().map(|op| self.encode_operand_snap(op)).collect();
                    let pure_func_app = pure_func.function_ref.apply(self.vcx, &func_args);
                    let return_ty = destination.ty(self.local_decls, self.vcx.tcx()).ty;
                    let method_assign = self.deps.require_ref::<PredicateEnc>(
                        return_ty,
                    ).unwrap().method_assign;

                    self.stmt(self.vcx.alloc(method_assign.apply(self.vcx, [dest, pure_func_app])));
                } else {
                    let func_out = self.deps.require_ref::<MirImpureEnc>(
                        (task.0, task.1, Some(task.2)),
                    ).unwrap();

                    let method_in = args.iter().map(|op| self.encode_operand(op));
                    let method_args = std::iter::once(dest)
                        .chain(method_in)
                        .collect::<Vec<_>>();

                    self.stmt(self.vcx.alloc(func_out.method_ref.apply(self.vcx, &method_args)));
                }

                target.map(|target| self.vcx.mk_goto_stmt(
                    self.vcx.alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize()))
                )).unwrap_or_else(|| self.unreachable())
            }
            mir::TerminatorKind::Assert { cond, expected, target, unwind, .. } => {
                let e_bool = self.deps.require_ref::<PredicateEnc>(
                    self.vcx.tcx().types.bool,
                ).unwrap();
                let enc = self.encode_operand_snap(cond);
                let enc = e_bool.expect_prim().snap_to_prim.apply(self.vcx, [enc]);
                let expected = self.vcx.mk_const_expr(vir::ConstData::Bool(*expected));
                let assert = self.vcx.mk_bin_op_expr(vir::BinOpKind::CmpEq, enc, expected);
                self.stmt(self.vcx.mk_exhale_stmt(assert));

                let target_bb = self.vcx.alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize()));
                let otherwise = match unwind {
                    mir::UnwindAction::Cleanup(bb) =>
                        self.vcx.alloc(vir::CfgBlockLabelData::BasicBlock(bb.as_usize())),
                    _ => todo!()
                };

                self.vcx.mk_goto_if_stmt(enc, self.vcx.alloc_slice(&[self.vcx.mk_goto_if_target(
                    expected,
                    target_bb,
                    &[],
                )]), otherwise, &[])
            }
            mir::TerminatorKind::Unreachable => self.unreachable(),

            unsupported_kind => self.vcx.mk_dummy_stmt(
                vir::vir_format!(self.vcx, "terminator {unsupported_kind:?}")
            ),
        };
        assert!(self.current_terminator.replace(terminator).is_none());
    }
}
