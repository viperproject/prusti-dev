/*use prusti_rustc_interface::{
    middle::{mir, ty},
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
    UnsupportedStatement,
    UnsupportedTerminator,
}

#[derive(Clone, Debug)]
pub struct MirPureEncoderOutput<'vir> {
    pub expr: vir::Expr<'vir>,
}

use std::cell::RefCell;
thread_local! {
    static CACHE: task_encoder::CacheStaticRef<MirPureEncoder> = RefCell::new(Default::default());
}

struct MirPureEncoderInput<'vir, 'tcx> {
    pub parent_def_id: ty::WithOptConstParam<DefId>, // ID of the function
    pub promoted: mir::Promoted, // ID of a constant within the function
    pub param_env: ty::ParamEnv<'tcx>, // param environment at the usage site
    pub substs: ty::SubstsRef<'tcx>, // type substitutions at the usage site
}

impl TaskEncoder for MirPureEncoder {
    type TaskDescription<'vir, 'tcx> = ty::Ty<'tcx> where 'tcx: 'vir;

    type TaskKey<'vir, 'tcx> = (
        DefId, // ID of the function
        Option<mir::Promoted>, // ID of a constant within the function, or `None` if encoding the function itself
        ty::SubstsRef<'tcx>, // ? this should be the "signature", after applying the env/substs
    ) where 'tcx: 'vir;

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
        (
            // TODO
            task.parent_def_id.did,
            None,
            task.substs,
        )
    }

    fn task_to_output_ref<'vir, 'tcx>(_task: &Self::TaskDescription<'vir, 'tcx>) -> Self::OutputRef<'vir, 'tcx>
        where 'tcx: 'vir
    {
        () // TODO
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
        use bumpalo::collections::Vec as BumpVec; // TODO: re-export in vir?
        use bumpalo::vec as bvec; // TODO: re-export in vir?
        crate::with_vcx(|vcx| match task_key.kind() {
            TyKind::Bool => Ok((
                MirPureEncoderOutput {
                    snapshot: vcx.alloc(vir::DomainData {
                        name: vcx.alloc_str("s_Bool"),
                        axioms: bvec![in &vcx.arena//;
                            //vcx.alloc(vir::DomainAxiomData {
                            //    name: vcx.alloc_str("_"),
                            //    expr: 
                            //}),
                        ],
                        functions: bvec![in &vcx.arena;
                            vcx.alloc(vir::DomainFunctionData {
                                unique: false,
                                name: vcx.alloc_str("cons"),
                                args: bvec![in &vcx.arena;
                                    vcx.alloc(vir::TypeData::Bool),
                                ],
                                ret: vcx.alloc(vir::TypeData::Domain(vcx.alloc_str("s_Bool"))),
                            }),
                            crate::vir_domain_func! { vcx; function val(Domain[s_Bool]): Bool },
                            //vcx.alloc(vir::DomainFunctionData {
                            //    unique: false,
                            //    name: vcx.alloc_str("val"),
                            //    args: bvec![in &vcx.arena;
                            //        vcx.alloc(vir::TypeData::Domain(vcx.alloc_str("s_Bool"))),
                            //    ],
                            //    ret: vcx.alloc(vir::TypeData::Bool),
                            //}),
                        ],
                    }),
                    predicate: vcx.alloc(vir::PredicateData {
                        name: vcx.alloc_str("p_Bool"),
                        args: bvec![in &vcx.arena;
                            vcx.alloc(vir::LocalData {
                                name: vcx.alloc_str("self_p"),
                                ty: vcx.alloc(vir::TypeData::Ref),
                            }),
                            vcx.alloc(vir::LocalData {
                                name: vcx.alloc_str("self_s"),
                                ty: vcx.alloc(vir::TypeData::Domain(vcx.alloc_str("s_Bool"))),
                            }),
                        ],
                        expr: None,
                    }),
                },
                (),
            )),
            _ => Err((MirPureEncoderError::UnsupportedType, None)),
        })
    }
}
*/