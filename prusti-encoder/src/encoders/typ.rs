use prusti_rustc_interface::{
    middle::ty,
    //span::def_id::DefId,
};
use rustc_type_ir::sty::TyKind;
use task_encoder::{
    TaskEncoder,
    TaskEncoderDependencies,
};
use crate::vir;

pub struct TypeEncoder;

#[derive(Clone, Debug)]
pub enum TypeEncoderError {
    UnsupportedType,
}

// TODO: the output should be/include vir::Type
#[derive(Clone, Debug)]
pub struct TypeEncoderOutputRef<'vir> {
    pub snapshot: &'vir str,
    pub predicate: &'vir str,
}
impl<'vir, 'tcx> task_encoder::OutputRefAny<'vir, 'tcx> for TypeEncoderOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct TypeEncoderOutput<'vir> {
    pub snapshot: vir::Domain<'vir>,
    pub predicate: vir::Predicate<'vir>,
}

use std::cell::RefCell;
thread_local! {
    static CACHE: task_encoder::CacheStaticRef<TypeEncoder> = RefCell::new(Default::default());
}

impl TaskEncoder for TypeEncoder {
    type TaskDescription<'vir, 'tcx> = ty::Ty<'tcx> where 'tcx: 'vir;

    type OutputRef<'vir, 'tcx> = TypeEncoderOutputRef<'vir> where 'tcx: 'vir;
    type OutputFullLocal<'vir, 'tcx> = TypeEncoderOutput<'vir> where 'tcx: 'vir;
    //type OutputFullDependency<'vir, 'tcx> = TypeEncoderOutputDep<'vir> where 'tcx: 'vir;

    type EncodingError = TypeEncoderError;

    fn with_cache<'vir, 'tcx, F, R>(f: F) -> R
        where 'tcx: 'vir, F: FnOnce(&'vir task_encoder::CacheRef<'vir, 'tcx, TypeEncoder>) -> R,
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

    /*
    fn task_to_output_ref<'vir, 'tcx>(task: &Self::TaskDescription<'vir, 'tcx>) -> Self::OutputRef<'vir, 'tcx>
        where 'tcx: 'vir
    {
        let (snapshot, predicate) = match task.kind() {
            TyKind::Bool => ("s_Bool", "p_Bool"),
            _ => panic!(),
        };
        crate::with_vcx(|vcx| TypeEncoderOutputDep {
            snapshot: vcx.alloc_str(snapshot),
            predicate: vcx.alloc_str(predicate),
        })
    }
    */

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
        crate::with_vcx(|vcx| match task_key.kind() {
            TyKind::Bool => {
                deps.emit_output_ref::<Self>(*task_key, TypeEncoderOutputRef {
                    snapshot: vcx.alloc_str("s_Bool"),
                    predicate: vcx.alloc_str("p_Bool"),
                });
                Ok((TypeEncoderOutput {
                    snapshot: crate::vir_domain! { vcx; domain s_Bool {
                        function cons(Bool): s_Bool;
                        function val(s_Bool): Bool;
                        axiom_inverse(cons, val);
                    } },
                    predicate: crate::vir_predicate! { vcx; predicate p_Bool(self_p: Ref, self_s: s_Bool) },
                }, ()))
            }
            TyKind::Tuple(tys) if tys.len() == 0 => {
                deps.emit_output_ref::<Self>(*task_key, TypeEncoderOutputRef {
                    snapshot: vcx.alloc_str("s_Tuple0"),
                    predicate: vcx.alloc_str("p_Tuple0"),
                });
                Ok((TypeEncoderOutput {
                    snapshot: crate::vir_domain! { vcx; domain s_Tuple0 {
                        function cons(): s_Tuple0;
                    } },
                    predicate: crate::vir_predicate! { vcx; predicate p_Tuple0(self_p: Ref, self_s: s_Tuple0) },
                }, ()))
            }
            TyKind::Adt(adt_def, substs) if adt_def.is_struct() => {
                let name_s = vcx.alloc_str("s_Adt_"); // TODO
                let name_p = vcx.alloc_str("p_Adt_"); // TODO
                deps.emit_output_ref::<Self>(*task_key, TypeEncoderOutputRef {
                    snapshot: name_s,
                    predicate: name_p,
                });
                let ty_s = vcx.alloc(vir::TypeData::Domain(name_s));
                let mut funcs: Vec<vir::DomainFunction<'vir>> = vec![];
                for (idx, field) in adt_def.all_fields().enumerate() {
                    let ty_out = deps.require_ref::<crate::encoders::TypeEncoder>(field.ty(vcx.tcx, substs)).unwrap();
                    let field_ty_s = vcx.alloc(vir::TypeData::Domain(ty_out.snapshot));

                    let name_r = vcx.alloc_str(&format!("read_field_{idx}"));
                    funcs.push(crate::vir_domain_func! { vcx; function [name_r]([ty_s]): [field_ty_s] });

                    let name_w = vcx.alloc_str(&format!("write_field_{idx}"));
                    funcs.push(crate::vir_domain_func! { vcx; function [name_w]([ty_s], [field_ty_s]): [ty_s] });
                }

                /*
                TODO: constructor

                TODO: axioms
                forall f0, f1, ...
                    read_field_0(cons(f0, f1, ...)) == f0
                    && read_field_1(cons(f0, f1, ...)) == f1
                    && ...
                forall f0, v
                    read_field_0(write_field_0(v, f0)) == f0
                    && read_field_1(write_field_0(v, f0)) == read_field_1(v)
                    && ...
                */

                Ok((TypeEncoderOutput {
                    snapshot: crate::vir_domain! { vcx; domain [name_s] {
                        with_funcs [funcs];
                    } },
                    predicate: crate::vir_predicate! { vcx; predicate [name_p](self_p: Ref, self_s: [ty_s]) },
                }, ()))
            }
            _ => Err((TypeEncoderError::UnsupportedType, None)),
        })
    }
}
