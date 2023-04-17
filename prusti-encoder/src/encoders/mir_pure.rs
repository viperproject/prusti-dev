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

pub struct MirPureEncoder;

#[derive(Clone, Debug)]
pub enum MirPureEncoderError {
    Unsupported,
}

#[derive(Clone, Debug)]
pub struct MirPureEncoderOutput<'vir> {
    function: vir::Function<'vir>,
}

use std::cell::RefCell;
thread_local! {
    static CACHE: task_encoder::CacheStaticRef<MirPureEncoder> = RefCell::new(Default::default());
}

impl TaskEncoder for MirPureEncoder {
    // TODO: local def id (+ promoted, substs, etc)
    type TaskDescription<'vir, 'tcx> = DefId where 'tcx: 'vir;

    type OutputFullLocal<'vir, 'tcx> = MirPureEncoderOutput<'vir> where 'tcx: 'vir;

    type EncodingError = MirPureEncoderError;

    fn with_cache<'vir, 'tcx, F, R>(f: F) -> R
        where 'tcx: 'vir, F: FnOnce(&'vir task_encoder::CacheRef<'vir, 'tcx, MirPureEncoder>) -> R,
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

            // Local count for the Viper method:
            // - one for each basic block;
            // - two (`Ref`, initial snapshot) for each non-argument,
            //   non-return local.
            let local_count = block_count + 2 * (body.local_decls.len() - body.arg_count - 1);

            let mut args = vir::BumpVec::with_capacity_in(arg_count, &vcx.arena);
            for arg_idx in 1..=body.arg_count {
                let name_p = vcx.alloc_str(&format!("_{}p", arg_idx));
                let name_s = vcx.alloc_str(&format!("_{}s_init", arg_idx));
                let ty_s = vcx.alloc(vir::TypeData::Domain(local_types[arg_idx.into()]));
                args.push(crate::vir_local_decl! { vcx; [name_p] : Ref });
                args.push(crate::vir_local_decl! { vcx; [name_s] : [ty_s] });
            }

            let mut visitor = EncoderVisitor {
                vcx,
                local_types,
                current_block: None
            };
            visitor.visit_body(&body);

            Ok((MirPureEncoderOutput {
                function: vcx.alloc(vir::FunctionData {
                    name: vcx.alloc_str(&format!("f_{}", vcx.tcx.item_name(*def_id))),
                    args,
                    pres: vir::bvec![in &vcx.arena],
                    posts: vir::bvec![in &vcx.arena],
                    expr: None
                }),
            }, ()))
        })
    }
}

struct EncoderVisitor<'vir, 'tcx> {
    vcx: &'vir vir::VirCtxt<'tcx>,
    local_types: IndexVec<mir::Local, &'vir str>,
    current_block: Option<vir::BumpVec<'vir, vir::Stmt<'vir>>>
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
    }

    fn visit_statement(
        &mut self,
        statement: &mir::Statement<'tcx>,
        location: mir::Location,
    ) {
        match &statement.kind {
            mir::StatementKind::Assign(box (place, rvalue)) => {
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
