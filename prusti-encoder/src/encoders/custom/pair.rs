use task_encoder::TaskEncoder;

pub struct PairUseEnc;

// TODO: remove this once used
#[allow(unused)]
#[derive(Debug, Clone)]
pub struct PairUse<'vir> {
    pub ty: vir::TypePair<'vir>,
    pub constructor: vir::FunctionIdn<'vir, vir::ManyDyn, vir::Pair>,
    pub destructors: Vec<vir::AdtDestructor<'vir, vir::Pair, vir::Dyn>>,
}

impl TaskEncoder for PairUseEnc {
    task_encoder::encoder_cache!(PairUseEnc);
    const ENCODER_NAME: &'static str = "pair use encoder";
    type TaskDescription<'vir> = Vec<vir::TypeDyn<'vir>>;
    type OutputFullDependency<'vir> = PairUse<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        task.clone()
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(task_key.clone(), ())?;
        let tuple = deps.require_dep::<PairEnc>(task_key.len())?;

        vir::with_vcx(|vcx| {
            let params = vcx.alloc_slice(task_key);
            let ty = (tuple.self_ty)(params);

            let constructor =
                vir::FunctionIdn::new(vir::ViperIdent::new(tuple.constructor.name), params, ty);

            let destructors = tuple
                .constructor
                .args
                .iter()
                .zip(params)
                .map(|(local, field)| vcx.mk_adt_destructor(local.name, ty, field))
                .collect::<Vec<_>>();
            Ok((
                (),
                PairUse {
                    ty,
                    constructor,
                    destructors,
                },
            ))
        })
    }
}

#[derive(Debug, Clone)]
struct Pair<'vir> {
    self_ty: vir::DomainIdn<'vir, vir::Pair>,
    constructor: vir::AdtConstructor<'vir>,
}

struct PairEnc;

impl TaskEncoder for PairEnc {
    task_encoder::encoder_cache!(PairEnc);
    const ENCODER_NAME: &'static str = "pair encoder";

    type TaskDescription<'vir> = usize;
    type OutputFullDependency<'vir> = Pair<'vir>;
    type OutputFullLocal<'vir> = vir::Adt<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        vir::with_vcx(|vcx| {
            let idn = vir::ViperIdent::new(vir::vir_format!(vcx, "Pair{}", *task_key));
            let self_ty = vir::DomainIdn::new(idn, *task_key);
            let typarams = (0..*task_key)
                .map(|i| {
                    vcx.alloc(vir::DomainParamData {
                        name: vir::vir_format!(vcx, "Ty{}", i),
                        index: i,
                    })
                })
                .collect::<Vec<_>>();
            let typarams = vcx.alloc_slice(&typarams);
            let locals = typarams
                .iter()
                .enumerate()
                .map(|(i, dpd)| {
                    let dt = vir::TypeKind::DomainTypeParam(**dpd);
                    let ty = vcx.alloc(vir::TypeData::<vir::Dyn>::new(dt));
                    vcx.mk_local_decl(vir::vir_format!(vcx, "_{task_key}_{i}"), ty)
                })
                .collect::<Vec<_>>();
            let locals = vcx.alloc_slice(&locals);
            let constructor =
                vcx.mk_adt_constructor(vir::vir_format!(vcx, "T{}", *task_key), locals);
            let constructors = vcx.alloc_array(&[constructor]);
            let adt = vcx.mk_adt(idn, typarams, constructors);

            Ok((
                adt,
                Pair {
                    self_ty,
                    constructor,
                },
            ))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        let outputs = Self::all_outputs_local_no_errors(program);
        for output in outputs {
            program.add_adt(output);
        }
    }
}
