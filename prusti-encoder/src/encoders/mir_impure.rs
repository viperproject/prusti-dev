use prusti_rustc_interface::{
    index::vec::IndexVec,
    middle::ty,
    middle::mir,
    span::def_id::DefId,
};
use mir_state_analysis::{
    free_pcs::{FreePcsAnalysis, FreePcsCursor},
};
use task_encoder::{
    TaskEncoder,
    TaskEncoderDependencies,
};
use std::collections::HashMap;
use crate::vir;

pub struct MirImpureEncoder;

#[derive(Clone, Debug)]
pub enum MirImpureEncoderError {
    Unsupported,
}

#[derive(Clone, Debug)]
pub struct MirImpureEncoderOutput<'vir> {
    pub method: vir::Method<'vir>,
}

use std::cell::RefCell;
thread_local! {
    static CACHE: task_encoder::CacheStaticRef<MirImpureEncoder> = RefCell::new(Default::default());
}

impl TaskEncoder for MirImpureEncoder {
    // TODO: local def id (+ promoted, substs, etc)
    type TaskDescription<'vir, 'tcx> = DefId where 'tcx: 'vir;

    type OutputFullLocal<'vir, 'tcx> = MirImpureEncoderOutput<'vir> where 'tcx: 'vir;

    type EncodingError = MirImpureEncoderError;

    fn with_cache<'vir, 'tcx, F, R>(f: F) -> R
        where 'tcx: 'vir, F: FnOnce(&'vir task_encoder::CacheRef<'vir, 'tcx, MirImpureEncoder>) -> R,
    {
        CACHE.with(|cache| {
            // SAFETY: the 'vir and 'tcx given to this function will always be
            //   the same (or shorter) than the lifetimes of the VIR arena and
            //   the rustc type context, respectively
            let cache = unsafe { std::mem::transmute(cache) };
            f(cache)
        })
    }

    fn task_to_key<'vir, 'tcx>(task: &Self::TaskDescription<'vir, 'tcx>) -> Self::TaskKey<'vir, 'tcx>
        where 'tcx: 'vir
    {
        *task
    }

    fn do_encode_full<'vir, 'tcx>(
        task_key: &Self::TaskKey<'vir, 'tcx>,
        deps: &mut TaskEncoderDependencies<'vir, 'tcx>,
    ) -> Result<(
        Self::OutputFullLocal<'vir, 'tcx>,
        Self::OutputFullDependency<'vir, 'tcx>,
    ), (
        Self::EncodingError,
        Option<Self::OutputFullDependency<'vir, 'tcx>>,
    )> {
        deps.emit_output_ref::<Self>(*task_key, ());

        use mir::visit::Visitor;
        crate::with_vcx(|vcx| {
            let def_id = task_key;
            let local_def_id = def_id.expect_local();
            let body = vcx.tcx.mir_promoted(ty::WithOptConstParam::unknown(local_def_id)).0.borrow();

            let mut ssa_visitor = SsaVisitor::new(vcx, body.local_decls.len());
            ssa_visitor.analyse(&body);
            let ssa_analysis = ssa_visitor.analysis;

            let fpcs_analysis = mir_state_analysis::run_free_pcs(&body, vcx.tcx);

            let local_types = body.local_decls.iter()
                .map(|local_decl| deps.require_ref::<crate::encoders::TypeEncoder>(
                    local_decl.ty,
                ).unwrap())
                .collect::<IndexVec<mir::Local, _>>();

            let block_count = body.basic_blocks.postorder().len();

            // Argument count for the Viper method:
            // - two (`Ref`, initial snapshot) for the return place;
            // - two (`Ref`, initial snapshot) for each MIR argument.
            //
            // Note that the return place is modelled as an argument of the
            // Viper method. This corresponds to an execution model where the
            // method can return data to the caller without a copy--it directly
            // modifies a place provided by the caller.
            //
            // TODO: type parameters
            let arg_count = 2 + 2 * body.arg_count;

            // Return count for the Viper method:
            // - TODO: updated arguments
            // - one (final snapshot) for the return place.
            let ret_count = 1;

            // Local count for the Viper method:
            // - one for each basic block;
            // - two (`Ref`, initial snapshot) for each non-argument,
            //   non-return local.
            let local_count = block_count + 2 * (body.local_decls.len() - body.arg_count - 1);

            let mut encoded_blocks = vir::BumpVec::with_capacity_in(
                // extra blocks: Start, End
                2 + block_count,
                &vcx.arena,
            );
            let mut pres = vir::bvec![in &vcx.arena]; // TODO: capacity
            let start_stmts = vir::BumpVec::from_iter_in(
                (body.arg_count + 1..body.local_decls.len())
                    .map(|local| {
                        let name_p = crate::vir_format!(vcx, "_{local}p");
                        let name_s = crate::vir_format!(vcx, "_{local}s_0");
                        let ty_s = local_types[local.into()].snapshot;
                        vec![
                            vcx.alloc(vir::StmtData::LocalDecl(
                                crate::vir_local_decl! { vcx; [name_p] : Ref },
                            )),
                            vcx.alloc(vir::StmtData::LocalDecl(
                                crate::vir_local_decl! { vcx; [name_s] : [ty_s] },
                            )),
                            vcx.alloc(vir::StmtData::Inhale(
                                vcx.alloc(vir::ExprData::PredicateApp(vcx.alloc(vir::PredicateAppData {
                                    target: local_types[local.into()].predicate_name,
                                    args: vir::bvec![in &vcx.arena;
                                        vcx.mk_local_ex(name_p),
                                        vcx.mk_local_ex(name_s),
                                    ],
                                })))
                            )),
                        ]
                    })
                    .flatten()
                    .chain((0..block_count)
                        .map(|block| {
                            let name = crate::vir_format!(vcx, "_reach_bb{block}");
                            vcx.alloc(vir::StmtData::LocalDecl(vcx.alloc(vir::LocalDeclData {
                                name,
                                ty: vcx.alloc(vir::TypeData::Bool),
                                expr: Some(vcx.alloc(vir::ExprData::Todo("false"))),
                            })))
                        })),
                &vcx.arena,
            );
            encoded_blocks.push(vcx.alloc(vir::CfgBlockData {
                label: vcx.alloc(vir::CfgBlockLabelData::Start),
                stmts: start_stmts,
                terminator: vcx.alloc(vir::TerminatorStmtData::Goto(
                    vcx.alloc(vir::CfgBlockLabelData::BasicBlock(0)),
                )),
            }));

            let mut args = vir::BumpVec::with_capacity_in(arg_count * 2, &vcx.arena);
            for arg_idx in 0..=body.arg_count {
                let name_p = crate::vir_format!(vcx, "_{arg_idx}p");
                let name_s = crate::vir_format!(vcx, "_{arg_idx}s_0");
                let ty_s = local_types[arg_idx.into()].snapshot;
                args.push(crate::vir_local_decl! { vcx; [name_p] : Ref });
                args.push(crate::vir_local_decl! { vcx; [name_s] : [ty_s] });
                pres.push(vcx.alloc(vir::ExprData::PredicateApp(vcx.alloc(vir::PredicateAppData {
                    target: local_types[arg_idx.into()].predicate_name,
                    args: vir::bvec![in &vcx.arena;
                        vcx.mk_local_ex(name_p),
                        vcx.mk_local_ex(name_s),
                    ],
                }))));
            }

            let mut posts = vir::bvec![in &vcx.arena]; // TODO: capacity
            let mut rets = vir::BumpVec::with_capacity_in(ret_count, &vcx.arena);
            {
                let ty_s = local_types[0usize.into()].snapshot;
                rets.push(crate::vir_local_decl! { vcx; _0s_final : [ty_s] });
                posts.push(vcx.alloc(vir::ExprData::PredicateApp(vcx.alloc(vir::PredicateAppData {
                    target: local_types[0usize.into()].predicate_name,
                    args: vir::bvec![in &vcx.arena;
                        vcx.mk_local_ex("_0p"),
                        vcx.mk_local_ex("_0s_final"),
                    ],
                }))));
            };

            let mut visitor = EncoderVisitor {
                vcx,
                deps,
                local_decls: &body.local_decls,
                ssa_analysis,
                fpcs_analysis,
                local_types,

                //current_fpcs: None,
                current_fpcs_stmt: Vec::new(),
                current_fpcs_term: HashMap::new(),

                current_stmts: None,
                current_terminator: None,
                encoded_blocks,
            };
            visitor.visit_body(&body);

            visitor.encoded_blocks.push(vcx.alloc(vir::CfgBlockData {
                label: vcx.alloc(vir::CfgBlockLabelData::End),
                stmts: vir::bvec![in &vcx.arena],
                terminator: vcx.alloc(vir::TerminatorStmtData::Exit),
            }));

            Ok((MirImpureEncoderOutput {
                method: vcx.alloc(vir::MethodData {
                    name: crate::vir_format!(vcx, "m_{}", vcx.tcx.item_name(*def_id)),
                    args,
                    rets,
                    pres,
                    posts,
                    blocks: Some(visitor.encoded_blocks),
                }),
            }, ()))
        })
    }
}

struct EncoderVisitor<'vir, 'tcx, 'enc>
    where 'tcx: 'vir, 'vir: 'enc
{
    vcx: &'vir vir::VirCtxt<'tcx>,
    deps: &'enc mut TaskEncoderDependencies<'vir, 'tcx>,
    local_decls: &'enc mir::LocalDecls<'tcx>,
    ssa_analysis: SsaAnalysis,
    fpcs_analysis: FreePcsAnalysis<'enc, 'tcx>,
    local_types: IndexVec<mir::Local, crate::encoders::TypeEncoderOutputRef<'vir>>,

    // for the current basic block
    //current_fpcs: Option<FreePcsCursor<'enc, 'enc, 'tcx>>, // TODO: lifetimes ...
    current_fpcs_stmt: Vec<Vec<mir_state_analysis::free_pcs::RepackOp<'tcx>>>,
    current_fpcs_term: HashMap<mir::BasicBlock, Vec<mir_state_analysis::free_pcs::RepackOp<'tcx>>>,

    current_stmts: Option<vir::BumpVec<'vir, vir::Stmt<'vir>>>,
    current_terminator: Option<vir::TerminatorStmt<'vir>>,

    encoded_blocks: vir::BumpVec<'vir, vir::CfgBlock<'vir>>, // TODO: use IndexVec ?
}

impl<'vir, 'tcx, 'enc> EncoderVisitor<'vir, 'tcx, 'enc> {
    fn stmt(&mut self, stmt: vir::StmtData<'vir>) {
        self.current_stmts
            .as_mut()
            .unwrap()
            .push(self.vcx.alloc(stmt));
    }

    fn project_write_snap(
        &mut self,
        old_base: vir::Expr<'vir>,
        ty_out: crate::encoders::TypeEncoderOutputRef<'vir>,
        val: vir::Expr<'vir>,
        projection: &'tcx ty::List<mir::PlaceElem<'tcx>>,
    ) -> vir::Expr<'vir> {
        // A nested field update like:
        //     _1.x.y := 42
        //
        // Each field update overrides the full snapshot, thus the above is:
        //     _1.x := (y := 42, other := old(_1.x.other))
        //     _1   := (x := (y := 42, other := old(_1.x.other)), other := old(_1.other))
        //
        // In terms of generated functions:
        //     _1   := write_x(old(_1), write_y(read_x(old(_1)), 42))
        //
        // This function generates the above expression, given `old(_1)` in the
        // `old_base` argument, the target value in the `val` argument, and the
        // projections in the `projection` argument.

        // TODO: this is an rfold maybe?
        fn rec<'vir, 'tcx, 'enc>(
            vcx: &'vir vir::VirCtxt<'tcx>,
            deps: &'enc mut TaskEncoderDependencies<'vir, 'tcx>,
            old_base: vir::Expr<'vir>,
            ty_out: crate::encoders::TypeEncoderOutputRef<'vir>,
            val: vir::Expr<'vir>,
            projection: &'tcx ty::List<mir::PlaceElem<'tcx>>,
            pos: usize,
        ) -> vir::Expr<'vir>
            where 'tcx: 'vir, 'vir: 'enc
        {
            if pos >= projection.len() {
                return val;
            }
            match projection[pos] {
                mir::ProjectionElem::Field(f, ty) => {
                    let field_ty_out = deps.require_ref::<crate::encoders::TypeEncoder>(
                        ty,
                    ).unwrap();
                    // write_{f}(old_base, projection(read_{f}(old_base), val, projection, pos + 1))
                    vcx.alloc(vir::ExprData::FuncApp(vcx.alloc(vir::FuncAppData {
                        target: ty_out.field_write[f.as_usize()],
                        args: vir::bvec![in &vcx.arena;
                            old_base,
                            rec(
                                vcx,
                                deps,
                                vcx.alloc(vir::ExprData::FuncApp(vcx.alloc(vir::FuncAppData {
                                    target: ty_out.field_read[f.as_usize()],
                                    args: vir::bvec![in &vcx.arena;
                                        old_base,
                                    ],
                                }))),
                                field_ty_out,
                                val,
                                projection,
                                pos + 1
                            ),
                        ],
                    })))
                }
                _ => panic!("unsupported projection"),
            }
        }
        rec(self.vcx, self.deps, old_base, ty_out, val, projection, 0usize)
    }

    fn project_read_snap(
        &mut self,
        base: vir::Expr<'vir>,
        ty_out: crate::encoders::TypeEncoderOutputRef<'vir>,
        projection: &'tcx ty::List<mir::PlaceElem<'tcx>>,
    ) -> vir::Expr<'vir> {
        projection.iter()
            .fold((base, ty_out), |(base, ty_out), proj| match proj {
                mir::ProjectionElem::Field(f, ty) => {
                    let field_ty_out = self.deps.require_ref::<crate::encoders::TypeEncoder>(
                        ty,
                    ).unwrap();
                    (self.vcx.alloc(vir::ExprData::FuncApp(self.vcx.alloc(vir::FuncAppData {
                        target: ty_out.field_read[f.as_usize()],
                        args: vir::bvec![in &self.vcx.arena; base],
                    }))), field_ty_out)
                }
                _ => panic!("unsupported projection"),
            }).0
    }

    fn project(
        &mut self,
        base: vir::Expr<'vir>,
        ty_out: crate::encoders::TypeEncoderOutputRef<'vir>,
        projection: &'tcx ty::List<mir::PlaceElem<'tcx>>
    ) -> vir::Expr<'vir> {
        projection.iter()
            .fold((base, ty_out), |(base, ty_out), proj| match proj {
                mir::ProjectionElem::Field(f, ty) => {
                    let field_ty_out = self.deps.require_ref::<crate::encoders::TypeEncoder>(
                        ty,
                    ).unwrap();
                    (self.vcx.alloc(vir::ExprData::FuncApp(self.vcx.alloc(vir::FuncAppData {
                        target: ty_out.field_projection_p[f.as_usize()],
                        args: vir::bvec![in &self.vcx.arena; base],
                    }))), field_ty_out)
                }
                _ => panic!("unsupported projection"),
            }).0
    }

    fn fpcs_location(
        &mut self,
        location: mir::Location,
    ) {
        // TODO: no clone ...
        for repack_op in self.current_fpcs_stmt[location.statement_index].clone() {
            match repack_op {
                mir_state_analysis::free_pcs::RepackOp::Expand(place, _target, capability_kind)
                | mir_state_analysis::free_pcs::RepackOp::Collapse(place, _target, capability_kind) => {
                    
                    let place_ty = place.ty(self.local_decls, self.vcx.tcx);
                    assert!(place_ty.variant_index.is_none());

                    let place_ty_out = self.deps.require_ref::<crate::encoders::TypeEncoder>(
                        place_ty.ty,
                    ).unwrap();

                    let name_p = crate::vir_format!(self.vcx, "_{}p", place.local.index());
                    let ref_p = self.project(
                        self.vcx.mk_local_ex(name_p),
                        self.local_types[place.local].clone(),
                        place.projection,
                    );
                    let name_s = crate::vir_format!(
                        self.vcx,
                        "_{}s_{}",
                        place.local.index(),
                        self.ssa_analysis.version[&(location, place.local)],
                    );
                    let base_ty_out = &self.local_types[place.local];
                    let projection_s = self.project_read_snap(
                        self.vcx.mk_local_ex(name_s),
                        base_ty_out.clone(),
                        place.projection,
                    );
                    if matches!(repack_op, mir_state_analysis::free_pcs::RepackOp::Expand(..)) {
                        self.stmt(vir::StmtData::Unfold(self.vcx.alloc(vir::PredicateAppData {
                            target: place_ty_out.predicate_name,
                            args: vir::bvec![in &self.vcx.arena;
                                ref_p,
                                projection_s,
                            ],
                        })));
                    } else {
                        self.stmt(vir::StmtData::Fold(self.vcx.alloc(vir::PredicateAppData {
                            target: place_ty_out.predicate_name,
                            args: vir::bvec![in &self.vcx.arena;
                                ref_p,
                                projection_s,
                            ],
                        })));
                    }
                }
                unsupported_op => panic!("unsupported repack op: {unsupported_op:?}"),
            }
        }
    }
}

impl<'vir, 'tcx, 'enc> mir::visit::Visitor<'tcx> for EncoderVisitor<'vir, 'tcx, 'enc> {
    // fn visit_body(&mut self, body: &mir::Body<'tcx>) {
    //     println!("visiting body!");
    // }
    fn visit_basic_block_data(
        &mut self,
        block: mir::BasicBlock,
        data: &mir::BasicBlockData<'tcx>,
    ) {
        let mut fpcs_for_block = self.fpcs_analysis.analysis_for_bb(block);
        self.current_fpcs_stmt = (0..=data.statements.len())
            .map(|statement_index| {
                let location = mir::Location {
                    block,
                    statement_index,
                };
                let fpcs_for_stmt = fpcs_for_block.next().unwrap();
                assert_eq!(location, fpcs_for_stmt.location);
                fpcs_for_stmt.repacks.clone()
            })
            .collect::<Vec<_>>();
        println!("current_fpcs_stmt: {:?}", self.current_fpcs_stmt);
        let fpcs_for_term = fpcs_for_block.next().unwrap_err();
        self.current_fpcs_term = data.terminator().successors()
            .enumerate()
            .map(|(succ_idx, succ_block)| (
                succ_block,
                fpcs_for_term.succs[succ_idx].repacks.clone(),
            ))
            .collect::<HashMap<_, _>>();
        println!("current_fpcs_term: {:?}", self.current_fpcs_term);

        self.current_stmts = Some(vir::BumpVec::with_capacity_in(
            data.statements.len(), // TODO: not exact?
            &self.vcx.arena,
        ));
        self.stmt(vir::StmtData::PureAssign(self.vcx.alloc(vir::PureAssignData {
            dest: self.vcx.mk_local(crate::vir_format!(self.vcx, "_reach_bb{}", block.as_usize())),
            expr: self.vcx.alloc(vir::ExprData::Todo("true")),
        })));

        let mut phi_stmts = vec![];
        if let Some(phi_nodes) = self.ssa_analysis.phi.get(&block) {
            for phi_node in phi_nodes {
                assert!(!phi_node.sources.is_empty());
                let local_ty = &self.local_types[phi_node.local];
                let expr = phi_node.sources.iter()
                    .fold(self.vcx.alloc(vir::ExprData::FuncApp(self.vcx.alloc(vir::FuncAppData {
                        target: local_ty.function_unreachable,
                        args: vir::bvec![in &self.vcx.arena],
                    }))), |prev, source| self.vcx.alloc(vir::ExprData::Ternary(self.vcx.alloc(vir::TernaryData {
                        cond: self.vcx.mk_local_ex(crate::vir_format!(self.vcx, "_reach_bb{}", source.0.as_usize())),
                        then: self.vcx.mk_local_ex(crate::vir_format!(self.vcx, "_{}s_{}", phi_node.local.as_usize(), source.1)),
                        else_: prev,
                    }))));
                phi_stmts.push(vir::StmtData::LocalDecl(self.vcx.alloc(vir::LocalDeclData {
                    name: crate::vir_format!(self.vcx, "_{}s_{}", phi_node.local.as_usize(), phi_node.new_version),
                    ty: self.local_types[phi_node.local].snapshot,
                    expr: Some(expr),
                })));
            }
        }
        for phi_stmt in phi_stmts {
            self.stmt(phi_stmt);
        }

        assert!(self.current_terminator.is_none());
        self.super_basic_block_data(block, data);
        let stmts = self.current_stmts.take().unwrap();
        let terminator = self.current_terminator.take().unwrap();
        self.encoded_blocks.push(self.vcx.alloc(vir::CfgBlockData {
            label: self.vcx.alloc(vir::CfgBlockLabelData::BasicBlock(block.as_usize())),
            stmts,
            terminator,
        }));
    }

    fn visit_statement(
        &mut self,
        statement: &mir::Statement<'tcx>,
        location: mir::Location,
    ) {
        self.fpcs_location(location);
        match &statement.kind {
            mir::StatementKind::Assign(box (dest, rvalue)) => {
                let ssa_update = self.ssa_analysis.updates.get(&location).cloned().unwrap();
                assert!(ssa_update.local == dest.local);

                let dest_ty = dest.ty(self.local_decls, self.vcx.tcx);
                assert!(dest_ty.variant_index.is_none());
                let dest_ty_out = self.deps.require_ref::<crate::encoders::TypeEncoder>(
                    dest_ty.ty,
                ).unwrap();

                let name_p = crate::vir_format!(self.vcx, "_{}p", dest.local.index());
                let old_name_s = crate::vir_format!(self.vcx, "_{}s_{}", dest.local.index(), ssa_update.old_version);
                let name_s = crate::vir_format!(self.vcx, "_{}s_{}", dest.local.index(), ssa_update.new_version);
                let ty_s = self.local_types[ssa_update.local].snapshot;
                let expr = match rvalue {
                    mir::Rvalue::Use(
                        mir::Operand::Copy(source) | mir::Operand::Move(source)
                    ) => {
                        assert!(source.projection.is_empty());
                        let source_version = self.ssa_analysis.version.get(&(location, source.local)).unwrap();
                        let source_name = crate::vir_format!(self.vcx, "_{}s_{}", source.local.index(), source_version);
                        self.vcx.mk_local_ex(source_name)
                    }

                    mir::Rvalue::Use(
                        mir::Operand::Constant(box constant)
                    ) => {
                        match constant.literal {
                            mir::ConstantKind::Val(const_val, const_ty) => {
                                match const_ty.kind() {
                                    ty::TyKind::Tuple(tys) if tys.len() == 0 => self.vcx.alloc(vir::ExprData::Todo(
                                        crate::vir_format!(self.vcx, "s_Tuple0_cons()"),
                                    )),
                                    ty::TyKind::Int(ty::IntTy::I32) => self.vcx.alloc(vir::ExprData::Todo(
                                        crate::vir_format!(self.vcx, "s_Int_i32_cons({})", const_val.try_to_scalar_int().unwrap()),
                                    )),
                                    unsupported_ty => todo!("unsupported constant literal type: {unsupported_ty:?}"),
                                }
                            }
                            unsupported_literal => todo!("unsupported constant literal: {unsupported_literal:?}"),
                        }
                    }

                    //mir::Rvalue::Repeat(Operand<'tcx>, Const<'tcx>) => {}
                    //mir::Rvalue::Ref(Region<'tcx>, BorrowKind, Place<'tcx>) => {}
                    //mir::Rvalue::ThreadLocalRef(DefId) => {}
                    //mir::Rvalue::AddressOf(Mutability, Place<'tcx>) => {}
                    //mir::Rvalue::Len(Place<'tcx>) => {}
                    //mir::Rvalue::Cast(CastKind, Operand<'tcx>, Ty<'tcx>) => {}
                    //mir::Rvalue::BinaryOp(BinOp, Box<(Operand<'tcx>, Operand<'tcx>)>) => {}
                    //mir::Rvalue::CheckedBinaryOp(BinOp, Box<(Operand<'tcx>, Operand<'tcx>)>) => {}
                    //mir::Rvalue::NullaryOp(NullOp, Ty<'tcx>) => {}

                    mir::Rvalue::UnaryOp(
                        unop,
                        mir::Operand::Copy(source) | mir::Operand::Move(source)
                    ) => {
                        assert!(source.projection.is_empty());
                        let source_version = self.ssa_analysis.version.get(&(location, source.local)).unwrap();
                        let source_name = crate::vir_format!(self.vcx, "_{}s_{}", source.local.index(), source_version);

                        let unop_function = self.deps.require_ref::<crate::encoders::MirBuiltinEncoder>(
                            crate::encoders::MirBuiltinEncoderTask::UnOp(
                                *unop,
                                source.ty(self.local_decls, self.vcx.tcx).ty,
                            ),
                        ).unwrap().name;
                        self.vcx.alloc(vir::ExprData::FuncApp(self.vcx.alloc(vir::FuncAppData {
                            target: unop_function,
                            args: vir::bvec![in &self.vcx.arena; self.vcx.mk_local_ex(source_name)],
                        })))
                    }

                    //mir::Rvalue::Discriminant(Place<'tcx>) => {}
                    //mir::Rvalue::Aggregate(Box<AggregateKind<'tcx>>, IndexVec<FieldIdx, Operand<'tcx>>) => {}
                    //mir::Rvalue::ShallowInitBox(Operand<'tcx>, Ty<'tcx>) => {}
                    //mir::Rvalue::CopyForDeref(Place<'tcx>) => {}
                    _ => {
                        self.vcx.alloc(vir::ExprData::Todo(
                            crate::vir_format!(self.vcx, "rvalue {rvalue:?}"),
                        ))
                    }
                };
                let projection_ref = self.project(
                    self.vcx.mk_local_ex(name_p),
                    self.local_types[ssa_update.local].clone(),
                    dest.projection,
                );
                let projection_s_old = self.project_read_snap(
                    self.vcx.mk_local_ex(old_name_s),
                    self.local_types[ssa_update.local].clone(),
                    dest.projection,
                );
                let projection_s_new = self.project_read_snap(
                    self.vcx.mk_local_ex(name_s),
                    self.local_types[ssa_update.local].clone(),
                    dest.projection,
                );

                // apply projection to the snapshot update
                let expr = self.project_write_snap(
                        self.vcx.mk_local_ex(old_name_s),
                        self.local_types[ssa_update.local].clone(),
                        expr,
                        dest.projection,
                    );

                self.stmt(vir::StmtData::LocalDecl(self.vcx.alloc(vir::LocalDeclData {
                    name: name_s,
                    ty: ty_s,
                    expr: Some(expr),
                })));
                self.stmt(vir::StmtData::MethodCall(self.vcx.alloc(vir::MethodCallData {
                    targets: vir::bvec![in &self.vcx.arena],
                    method: dest_ty_out.method_refold,
                    args: vir::bvec![in &self.vcx.arena;
                        projection_ref,
                        projection_s_old,
                        projection_s_new,
                    ],
                })));
            }

            // no-ops ?
            mir::StatementKind::StorageLive(..)
            | mir::StatementKind::StorageDead(..) => {}

            // no-ops
            mir::StatementKind::FakeRead(_)
            | mir::StatementKind::Retag(..)
            //| mir::StatementKind::PlaceMention(_)
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
        self.fpcs_location(location);
        match &terminator.kind {
            mir::TerminatorKind::Goto { target } => {
                assert!(self.current_terminator.replace(
                    self.vcx.alloc(vir::TerminatorStmtData::Goto(
                        self.vcx.alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize())),
                    )),
                ).is_none());
            }
            mir::TerminatorKind::SwitchInt {
                discr: mir::Operand::Copy(discr) | mir::Operand::Move(discr),
                targets,
            } => {
                assert!(discr.projection.is_empty());
                let discr_version = self.ssa_analysis.version.get(&(location, discr.local)).unwrap();
                let discr_name = crate::vir_format!(self.vcx, "_{}s_{}", discr.local.index(), discr_version);

                let goto_targets = vir::BumpVec::from_iter_in(
                    targets.iter()
                        .map(|(value, target)| (
                            self.vcx.alloc(vir::ExprData::Todo(crate::vir_format!(self.vcx, "constant({value})"))),
                            self.vcx.alloc(vir::CfgBlockLabelData::BasicBlock(target.as_usize())),
                        )),
                    &self.vcx.arena,
                );
                let goto_otherwise = self.vcx.alloc(vir::CfgBlockLabelData::BasicBlock(
                    targets.otherwise().as_usize(),
                ));

                assert!(self.current_terminator.replace(
                    self.vcx.alloc(vir::TerminatorStmtData::GotoIf(self.vcx.alloc(vir::GotoIfData {
                        value: self.vcx.mk_local_ex(discr_name),
                        targets: goto_targets,
                        otherwise: goto_otherwise,
                    }))),
                ).is_none());
            }
            mir::TerminatorKind::Return => {
                // TODO: also for modified arguments
                self.stmt(vir::StmtData::PureAssign(self.vcx.alloc(vir::PureAssignData {
                    dest: self.vcx.mk_local("_0s_final"),
                    expr: self.vcx.mk_local_ex(crate::vir_format!(self.vcx, "_0s_{}", self.ssa_analysis.version[&(location, 0usize.into())])),
                })));

                assert!(self.current_terminator.replace(
                    self.vcx.alloc(vir::TerminatorStmtData::Goto(
                        self.vcx.alloc(vir::CfgBlockLabelData::End),
                    )),
                ).is_none());
            }
            unsupported_kind => {
                assert!(self.current_terminator.replace(
                    self.vcx.alloc(vir::TerminatorStmtData::Dummy(
                        crate::vir_format!(self.vcx, "terminator {unsupported_kind:?}"),
                    )),
                ).is_none());
            }
        }
    }
}

// THIS SSA ANALYSIS IS DISGUSTING (:
// TODO: make nicer, support cycles, move into a module

type SsaVersion = usize;

#[derive(Debug, Clone)]
struct SsaUpdate {
    local: mir::Local,
    old_version: SsaVersion,
    new_version: SsaVersion,
}

#[derive(Debug)]
struct SsaPhi {
    local: mir::Local,
    new_version: SsaVersion,
    sources: Vec<(mir::BasicBlock, SsaVersion)>,
}

#[derive(Debug)]
struct SsaAnalysis {
    version: HashMap<(mir::Location, mir::Local), SsaVersion>,
    updates: HashMap<mir::Location, SsaUpdate>,
    phi: HashMap<mir::BasicBlock, Vec<SsaPhi>>,
}
struct SsaVisitor<'vir, 'tcx> {
    vcx: &'vir vir::VirCtxt<'tcx>,

    version_counter: IndexVec<mir::Local, SsaVersion>,
    last_version: IndexVec<mir::Local, SsaVersion>,
    block_started: Vec<bool>,
    initial_version_in_block: Vec<Option<IndexVec<mir::Local, SsaVersion>>>,
    final_version_in_block: Vec<Option<IndexVec<mir::Local, SsaVersion>>>,
    local_count: usize,

    analysis: SsaAnalysis,
}

impl<'tcx, 'vir> SsaVisitor<'tcx, 'vir>
    where 'tcx: 'vir
{
    fn new(vcx: &'vir vir::VirCtxt<'tcx>, local_count: usize) -> Self {
        Self {
            vcx,

            version_counter: IndexVec::from_raw(vec![0; local_count]),
            last_version: IndexVec::from_raw(vec![0; local_count]),
            block_started: vec![],
            initial_version_in_block: vec![],
            final_version_in_block: vec![],
            local_count,

            analysis: SsaAnalysis {
                version: HashMap::new(),
                updates: HashMap::new(),
                phi: HashMap::new(),
            },
        }
    }

    // TODO: merge with new ...
    fn analyse<'a>(&mut self, body: &'a mir::Body<'tcx>) {
        for block in body.basic_blocks.postorder() {
            self.block_started.push(false);
            self.initial_version_in_block.push(None);
            self.final_version_in_block.push(None);
        }
        self.walk_block(body, 0usize.into());
    }

    fn walk_block<'a>(
        &mut self,
        body: &'a mir::Body<'tcx>,
        block: mir::BasicBlock,
    ) {
        if self.final_version_in_block[block.as_usize()].is_some() {
            return;
        }
        if self.block_started[block.as_usize()] {
            panic!("cycle in cfg!");
        }

        self.block_started[block.as_usize()] = true;

        let mut initial_versions = IndexVec::new();
        let mut phis = vec![];
        for local in 0..self.local_count {
            let mut prev_versions: Vec<(
                mir::BasicBlock, // origin
                SsaVersion,
            )> = vec![];
            for pred in &body.basic_blocks.predecessors()[block] { // TODO: iterator
                self.walk_block(body, *pred);
                // TODO: cfg cycles
                prev_versions.push((
                    *pred,
                    self.final_version_in_block[pred.as_usize()].as_ref().unwrap()[local.into()],
                ));
            }
            if prev_versions.is_empty() {
                initial_versions.push(0usize);
            } else {
                if prev_versions.iter().all(|v| v.1 == prev_versions[0].1) {
                    initial_versions.push(prev_versions[0].1);
                } else {
                    let new_version = self.last_version[local.into()] + 1;
                    self.last_version[local.into()] = new_version;
                    phis.push(SsaPhi {
                        local: local.into(),
                        new_version,
                        sources: prev_versions,
                    });
                    initial_versions.push(new_version);
                }
            }
        }
        if !phis.is_empty() {
            assert!(self.analysis.phi.insert(block, phis).is_none());
        }

        assert!(self.initial_version_in_block[block.as_usize()].replace(initial_versions.clone()).is_none());

        use mir::visit::Visitor;
        self.last_version = initial_versions;
        self.visit_basic_block_data(block, &body[block]);

        let final_versions = (0..self.local_count)
            .map(|local| self.last_version[local.into()])
            .collect::<IndexVec<_, _>>();
        for local in 0..self.local_count {
            self.analysis.version.insert((
                body.terminator_loc(block),
                local.into(),
            ), final_versions[local.into()]);
        }
        assert!(self.final_version_in_block[block.as_usize()].replace(final_versions).is_none());

        use prusti_rustc_interface::data_structures::graph::WithSuccessors;
        for succ in body.basic_blocks.successors(block) {
            if !self.block_started[succ.as_usize()] {
                self.walk_block(body, succ);
            }
        }
    }
}

impl<'tcx, 'vir> mir::visit::Visitor<'tcx> for SsaVisitor<'vir, 'tcx> {
    fn visit_place(
        &mut self,
        place: &mir::Place<'tcx>,
        context: mir::visit::PlaceContext,
        location: mir::Location,
    ) {
        let local = place.local;

        assert!(self.analysis.version
            .insert((location, local), self.last_version[local])
            .is_none());

        if let mir::visit::PlaceContext::MutatingUse(_) = context {
            let old_version = self.last_version[local];
            let new_version = self.version_counter[local] + 1;
            self.version_counter[local] = new_version;
            self.last_version[local] = new_version;
            assert!(self.analysis.updates
                .insert(location, SsaUpdate {
                    local,
                    old_version,
                    new_version,
                })
                .is_none());
        }
    }
}
