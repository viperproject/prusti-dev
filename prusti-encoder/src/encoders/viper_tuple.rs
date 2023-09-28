use task_encoder::{
    TaskEncoder,
    TaskEncoderDependencies,
};
use std::cell::RefCell;

pub struct ViperTupleEncoder;

#[derive(Clone, Debug)]
pub struct ViperTupleEncoderOutputRef<'vir> {
    pub elem_count: usize,
    pub domain_name: &'vir str,
    pub cons_name: &'vir str,
    pub elem_names: &'vir [&'vir str],
}
impl<'vir> task_encoder::OutputRefAny<'vir> for ViperTupleEncoderOutputRef<'vir> {}

impl<'vir> ViperTupleEncoderOutputRef<'vir> {
    pub fn mk_cons<Curr, Next>(
        &self,
        vcx: &'vir vir::VirCtxt<'vir>,
        elems: &[vir::ExprGen<'vir, Curr, Next>]
    ) -> vir::ExprGen<'vir, Curr, Next> {
        if self.elem_count == 1 {
            return elems[0];
        }
        vcx.mk_func_app(self.cons_name, elems)
    }

    pub fn mk_elem<Curr, Next>(
        &self,
        vcx: &'vir vir::VirCtxt<'vir>,
        tuple: vir::ExprGen<'vir, Curr, Next>,
        elem: usize,
    ) -> vir::ExprGen<'vir, Curr, Next> {
        assert!(elem < self.elem_count);
        if self.elem_count == 1 {
            return tuple;
        }
        vcx.mk_func_app(self.elem_names[elem], &[tuple])
    }
}

#[derive(Clone, Debug)]
pub struct ViperTupleEncoderOutput<'vir> {
    pub domain: Option<vir::Domain<'vir>>,
}

thread_local! {
    static CACHE: task_encoder::CacheStaticRef<ViperTupleEncoder> = RefCell::new(Default::default());
}

impl TaskEncoder for ViperTupleEncoder {
    type TaskDescription<'vir> = usize;

    type OutputRef<'vir> = ViperTupleEncoderOutputRef<'vir>;
    type OutputFullLocal<'vir> = ViperTupleEncoderOutput<'vir>;
    type EncodingError = ();

    fn with_cache<'vir, F, R>(f: F) -> R
       where F: FnOnce(&'vir task_encoder::CacheRef<'vir, ViperTupleEncoder>) -> R,
    {
        CACHE.with(|cache| {
            // SAFETY: the 'vir and 'tcx given to this function will always be
            //   the same (or shorter) than the lifetimes of the VIR arena and
            //   the rustc type context, respectively
            let cache = unsafe { std::mem::transmute(cache) };
            f(cache)
        })
    }

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir>,
    ) -> Result<(
        Self::OutputFullLocal<'vir>,
        Self::OutputFullDependency<'vir>,
    ), (
        Self::EncodingError,
        Option<Self::OutputFullDependency<'vir>>,
    )> {
        vir::with_vcx(|vcx| {
            let domain_name = vir::vir_format!(vcx, "Tuple_{task_key}");
            let cons_name = vir::vir_format!(vcx, "Tuple_{task_key}_cons");
            let elem_names = (0..*task_key)
                .map(|idx| vir::vir_format!(vcx, "Tuple_{task_key}_elem_{idx}"))
                .collect::<Vec<_>>();
            deps.emit_output_ref::<Self>(*task_key, ViperTupleEncoderOutputRef {
                elem_count: *task_key,
                domain_name,
                cons_name,
                elem_names: vcx.alloc_slice(&elem_names),
            });
            let typaram_names = (0..*task_key)
                .map(|idx| vir::vir_format!(vcx, "T{idx}"))
                .collect::<Vec<_>>();
            let typaram_tys = vcx.alloc_slice(&typaram_names.iter()
                .map(|name| vcx.alloc(vir::TypeData::Domain(name)))
                .collect::<Vec<_>>());
            let domain_ty = vcx.alloc(vir::TypeData::DomainParams(domain_name, typaram_tys));
            let qvars_names = (0..*task_key)
                .map(|idx| vir::vir_format!(vcx, "elem{idx}"))
                .collect::<Vec<_>>();
            let qvars_decl = vcx.alloc_slice(&(0..*task_key)
                .map(|idx| vcx.mk_local_decl(qvars_names[idx], typaram_tys[idx]))
                .collect::<Vec<_>>());
            let qvars_ex = (0..*task_key)
                .map(|idx| vcx.mk_local_ex(qvars_names[idx]))
                .collect::<Vec<_>>();
            let cons_call = vcx.mk_func_app(
                cons_name,
                &qvars_names.iter()
                    .map(|qvar| vcx.mk_local_ex(qvar))
                    .collect::<Vec<_>>(),
            );
            let axiom = vcx.alloc(vir::DomainAxiomData {
                name: vir::vir_format!(vcx, "ax_Tuple_{task_key}_elem"),
                expr: vcx.alloc(vir::ExprData::Forall(vcx.alloc(vir::ForallData {
                    qvars: qvars_decl,
                    triggers: vcx.alloc_slice(&[vcx.alloc_slice(&[cons_call])]),
                    body: vcx.mk_conj(&(0..*task_key)
                        .map(|idx| vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                            kind: vir::BinOpKind::CmpEq,
                            lhs: vcx.mk_func_app(elem_names[idx], &[cons_call]),
                            rhs: qvars_ex[idx],
                        }))))
                        .collect::<Vec<_>>()),
                }))),
            });
            let elem_args = vcx.alloc_slice(&[domain_ty]);
            let mut functions = (0..*task_key)
                .map(|idx| vcx.alloc(vir::DomainFunctionData {
                    unique: false,
                    name: elem_names[idx],
                    args: elem_args,
                    ret: typaram_tys[idx],
                }))
                .collect::<Vec<_>>();
            functions.push(vcx.alloc(vir::DomainFunctionData {
                unique: false,
                name: cons_name,
                args: typaram_tys,
                ret: domain_ty,
            }));
            Ok((ViperTupleEncoderOutput {
                domain: Some(vcx.alloc(vir::DomainData {
                    name: domain_name,
                    typarams: vcx.alloc_slice(&typaram_names),
                    axioms: vcx.alloc_slice(&[axiom]),
                    functions: vcx.alloc_slice(&functions),
                })),
            }, ()))
        })
    }
}
