use task_encoder::{
    TaskEncoder,
    TaskEncoderDependencies,
};
use vir::{FunctionIdent, UnknownArity, CallableIdent, UnaryArity};
use std::cell::RefCell;

pub struct ViperTupleEncoder;

#[derive(Clone, Debug)]
pub struct ViperTupleEncoderOutputRef<'vir> {
    pub elem_count: usize,
    pub domain_type: vir::Type<'vir>,
    pub constructor: FunctionIdent<'vir, UnknownArity<'vir>>,
    pub elem_getters: &'vir [FunctionIdent<'vir, UnaryArity<'vir>>],
}
impl<'vir> task_encoder::OutputRefAny for ViperTupleEncoderOutputRef<'vir> {}

impl<'vir> ViperTupleEncoderOutputRef<'vir> {
    pub fn mk_cons<'tcx, Curr, Next>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        elems: &[vir::ExprGen<'vir, Curr, Next>]
    ) -> vir::ExprGen<'vir, Curr, Next> {
        if self.elem_count == 1 {
            return elems[0];
        }
        self.constructor.apply(vcx, elems)
    }

    pub fn mk_elem<'tcx, Curr, Next>(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
        tuple: vir::ExprGen<'vir, Curr, Next>,
        elem: usize,
    ) -> vir::ExprGen<'vir, Curr, Next> {
        assert!(elem < self.elem_count);
        if self.elem_count == 1 {
            return tuple;
        }
        self.elem_getters[elem].apply(vcx, [tuple])
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

    fn with_cache<'tcx, 'vir, F, R>(f: F) -> R
       where F: FnOnce(&'vir task_encoder::CacheRef<'tcx, 'vir, ViperTupleEncoder>) -> R,
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
        let is_unit_tuple = *task_key == 0;
        vir::with_vcx(|vcx| {
            let domain_name = vir::vir_format!(vcx, "Tuple_{task_key}");
            let cons_name = vir::vir_format!(vcx, "Tuple_{task_key}_cons");
            let elem_names = (0..*task_key)
                .map(|idx| vir::vir_format!(vcx, "Tuple_{task_key}_elem_{idx}"))
                .collect::<Vec<_>>();
            let typaram_names = (0..*task_key)
                .map(|idx| vir::vir_format!(vcx, "T{idx}"))
                .collect::<Vec<_>>();
            let typaram_tys = vcx.alloc_slice(&typaram_names.iter()
                .map(|name| vcx.alloc(vir::TypeData::Domain(name)))
                .collect::<Vec<_>>());
            let constructor = FunctionIdent::new(cons_name, UnknownArity::new(typaram_tys));
            let domain_type = vcx.alloc(vir::TypeData::Domain(domain_name));
            let elem_getters = elem_names.iter().map(|name| {
                FunctionIdent::new(name, UnaryArity::new([domain_type]))
            }).collect::<Vec<_>>();
            deps.emit_output_ref::<Self>(*task_key, ViperTupleEncoderOutputRef {
                elem_count: *task_key,
                domain_type,
                constructor,
                elem_getters: vcx.alloc_slice(&elem_getters),
            });
            let domain_ty = vcx.alloc(vir::TypeData::DomainParams(domain_name, typaram_tys));
            let qvars_names = (0..*task_key)
                .map(|idx| vir::vir_format!(vcx, "elem{idx}"))
                .collect::<Vec<_>>();
            let mut axioms = Vec::new();
            if !is_unit_tuple {
                let qvars_decl = vcx.alloc_slice(&(0..*task_key)
                    .map(|idx| vcx.mk_local_decl(qvars_names[idx], typaram_tys[idx]))
                    .collect::<Vec<_>>());
                let qvars_ex = (0..*task_key)
                    .map(|idx| vcx.mk_local_ex(qvars_names[idx]))
                    .collect::<Vec<_>>();
                let cons_call = constructor.apply(vcx,
                    &qvars_names.iter()
                        .map(|qvar| vcx.mk_local_ex(qvar))
                        .collect::<Vec<_>>(),
                );
                let axiom = vcx.mk_domain_axiom(
                    vir::vir_format!(vcx, "ax_Tuple_{task_key}_elem"),
                    vcx.mk_forall_expr(
                        qvars_decl,
                        vcx.alloc_slice(&[vcx.alloc_slice(&[cons_call])]),
                        vcx.mk_conj(&(0..*task_key)
                            .map(|idx| vcx.mk_bin_op_expr(vir::BinOpKind::CmpEq, elem_getters[idx].apply(vcx, [cons_call]), qvars_ex[idx]))
                            .collect::<Vec<_>>()
                        )
                    )
                );
                axioms.push(axiom);
            }
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
                domain: Some(vcx.mk_domain(
                    domain_name,
                    vcx.alloc_slice(&typaram_names),
                    vcx.alloc_slice(&axioms),
                    vcx.alloc_slice(&functions),
                )),
            }, ()))
        })
    }
}
