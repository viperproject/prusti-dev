use prusti_rustc_interface::{
    index::vec::IndexVec,
    middle::ty,
    middle::mir,
    span::def_id::DefId,
};
use task_encoder::{
    TaskEncoder,
    TaskEncoderDependencies,
};
use crate::vir;

pub struct MirImpureEncoder;

#[derive(Clone, Debug)]
pub enum MirImpureEncoderError {
    Unsupported,
}

#[derive(Clone, Debug)]
pub struct MirImpureEncoderOutput<'vir> {
    method: vir::Method<'vir>,
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
            ssa_visitor.visit_body(&body);
            let ssa_analysis = ssa_visitor.analysis;
            println!("ssa: {:#?}", ssa_analysis);

            let local_types = body.local_decls.iter()
                .map(|local_decl| deps.require_ref::<crate::encoders::TypeEncoder>(
                    local_decl.ty,
                ).unwrap().snapshot)
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
            let start_stmts = vir::BumpVec::from_iter_in(
                (body.arg_count + 1..body.local_decls.len())
                    .map(|local| {
                        let name_p = vcx.alloc_str(&format!("_{}p", local));
                        let name_s = vcx.alloc_str(&format!("_{}s_init", local));
                        let ty_s = vcx.alloc(vir::TypeData::Domain(local_types[local.into()]));
                        vec![
                            crate::vir_local_decl! { vcx; [name_p] : Ref },
                            crate::vir_local_decl! { vcx; [name_s] : [ty_s] },
                        ]
                    })
                    .flatten()
                    .map(|decl| vcx.alloc(vir::StmtData::LocalDecl(decl))),
                &vcx.arena,
            );
            encoded_blocks.push(vcx.alloc(vir::CfgBlockData {
                label: vcx.alloc(vir::CfgBlockLabelData::Start),
                stmts: start_stmts,
            }));

            let mut args = vir::BumpVec::with_capacity_in(arg_count, &vcx.arena);
            for arg_idx in 1..=body.arg_count {
                let name_p = vcx.alloc_str(&format!("_{}p", arg_idx));
                let name_s = vcx.alloc_str(&format!("_{}s_init", arg_idx));
                let ty_s = vcx.alloc(vir::TypeData::Domain(local_types[arg_idx.into()]));
                args.push(crate::vir_local_decl! { vcx; [name_p] : Ref });
                args.push(crate::vir_local_decl! { vcx; [name_s] : [ty_s] });
            }

            let mut rets = vir::BumpVec::with_capacity_in(ret_count, &vcx.arena);
            {
                let ty_s = vcx.alloc(vir::TypeData::Domain(local_types[0usize.into()]));
                rets.push(crate::vir_local_decl! { vcx; _0s_final : [ty_s] });
            };

            let mut visitor = EncoderVisitor {
                vcx,
                ssa_analysis,
                local_types,
                current_block: None,
                encoded_blocks,
            };
            visitor.visit_body(&body);

            visitor.encoded_blocks.push(vcx.alloc(vir::CfgBlockData {
                label: vcx.alloc(vir::CfgBlockLabelData::End),
                stmts: vir::bvec![in &vcx.arena],
            }));

            Ok((MirImpureEncoderOutput {
                method: vcx.alloc(vir::MethodData {
                    name: vcx.alloc_str(&format!("m_{}", vcx.tcx.item_name(*def_id))),
                    args,
                    rets,
                    pres: vir::bvec![in &vcx.arena],
                    posts: vir::bvec![in &vcx.arena],
                    blocks: visitor.encoded_blocks,
                }),
            }, ()))
        })
    }
}

struct EncoderVisitor<'vir, 'tcx> {
    vcx: &'vir vir::VirCtxt<'tcx>,
    ssa_analysis: SsaAnalysis,
    local_types: IndexVec<mir::Local, &'vir str>,
    current_block: Option<vir::BumpVec<'vir, vir::Stmt<'vir>>>,
    encoded_blocks: vir::BumpVec<'vir, vir::CfgBlock<'vir>>, // TODO: use IndexVec ?
}

impl<'tcx, 'vir> EncoderVisitor<'vir, 'tcx> {
    fn stmt(&mut self, stmt: vir::StmtData<'vir>) {
        self.current_block
            .as_mut()
            .unwrap()
            .push(self.vcx.alloc(stmt));
    }
}

impl<'tcx, 'vir> mir::visit::Visitor<'tcx> for EncoderVisitor<'vir, 'tcx> {
    // fn visit_body(&mut self, body: &mir::Body<'tcx>) {
    //     println!("visiting body!");
    // }
    fn visit_basic_block_data(
        &mut self,
        block: mir::BasicBlock,
        data: &mir::BasicBlockData<'tcx>,
    ) {
        self.current_block = Some(vir::BumpVec::with_capacity_in(
            data.statements.len(),
            &self.vcx.arena,
        ));
        self.super_basic_block_data(block, data);
        let stmts = self.current_block.take().unwrap();
        self.encoded_blocks.push(self.vcx.alloc(vir::CfgBlockData {
            label: self.vcx.alloc(vir::CfgBlockLabelData::BasicBlock(block.as_usize())),
            stmts,
        }));
    }

    fn visit_statement(
        &mut self,
        statement: &mir::Statement<'tcx>,
        location: mir::Location,
    ) {
        match &statement.kind {
            mir::StatementKind::Assign(box (place, rvalue)) => {
                assert!(place.projection.is_empty());
                let ssa_update = self.ssa_analysis.updates.get(&location).unwrap();
                assert!(ssa_update.0 == place.local);
                let name_s = self.vcx.alloc_str(&format!("_{}s_{}", place.local.index(), ssa_update.1));
                let ty_s = self.vcx.alloc(vir::TypeData::Domain(self.local_types[ssa_update.0]));
                self.stmt(vir::StmtData::LocalDecl(
                    crate::vir_local_decl! { self.vcx; [name_s] : [ty_s] },
                ));
                match rvalue {
                    //mir::Rvalue::Use(Operand<'tcx>) => {}
                    //mir::Rvalue::Repeat(Operand<'tcx>, Const<'tcx>) => {}
                    //mir::Rvalue::Ref(Region<'tcx>, BorrowKind, Place<'tcx>) => {}
                    //mir::Rvalue::ThreadLocalRef(DefId) => {}
                    //mir::Rvalue::AddressOf(Mutability, Place<'tcx>) => {}
                    //mir::Rvalue::Len(Place<'tcx>) => {}
                    //mir::Rvalue::Cast(CastKind, Operand<'tcx>, Ty<'tcx>) => {}
                    //mir::Rvalue::BinaryOp(BinOp, Box<(Operand<'tcx>, Operand<'tcx>)>) => {}
                    //mir::Rvalue::CheckedBinaryOp(BinOp, Box<(Operand<'tcx>, Operand<'tcx>)>) => {}
                    //mir::Rvalue::NullaryOp(NullOp, Ty<'tcx>) => {}
                    mir::Rvalue::UnaryOp(UnOp, Operand<'tcx>) => {
                        // require builtin mir_unop_neg/mir_unop_not
                        // apply func
                        todo!()
                    }
                    //mir::Rvalue::Discriminant(Place<'tcx>) => {}
                    //mir::Rvalue::Aggregate(Box<AggregateKind<'tcx>>, IndexVec<FieldIdx, Operand<'tcx>>) => {}
                    //mir::Rvalue::ShallowInitBox(Operand<'tcx>, Ty<'tcx>) => {}
                    //mir::Rvalue::CopyForDeref(Place<'tcx>) => {}
                    _ => {
                        self.stmt(vir::StmtData::Dummy(
                            self.vcx.alloc_str(&format!("rvalue {rvalue:?}"))
                        ));
                    }
                }
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
}

type SsaVersion = usize;

#[derive(Debug)]
struct SsaPhi {
    local: mir::Local,
    new_version: SsaVersion,
    cond: mir::BasicBlock,
    from_if: SsaVersion,
    from_else: SsaVersion,
}

#[derive(Debug)]
struct SsaAnalysis {
    updates: HashMap<mir::Location, (mir::Local, SsaVersion)>,
    phi: HashMap<mir::Location, Vec<SsaPhi>>,
}

use std::collections::HashMap;
struct SsaVisitor<'vir, 'tcx> {
    vcx: &'vir vir::VirCtxt<'tcx>,
    last_version: IndexVec<mir::Local, usize>,
    analysis: SsaAnalysis,
}

impl<'tcx, 'vir> SsaVisitor<'tcx, 'vir> {
    fn new(vcx: &'vir vir::VirCtxt<'tcx>, local_count: usize) -> Self {
        Self {
            vcx,
            last_version: IndexVec::from_raw(vec![0; local_count]),
            analysis: SsaAnalysis {
                updates: HashMap::new(),
                phi: HashMap::new(),
            },
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
        //println!(" ssa: {place:?} {context:?} {location:?}");
        if let mir::visit::PlaceContext::MutatingUse(_) = context {
            assert!(place.projection.is_empty());
            let local = place.local;
            let new_version = self.last_version[local] + 1;
            self.last_version[local] = new_version;
            assert!(self.analysis.updates
                .insert(location, (
                    local,
                    new_version,
                ))
                .is_none());
        }
    }
}
