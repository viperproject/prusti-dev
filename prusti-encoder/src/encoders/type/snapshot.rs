use prusti_rustc_interface::{
    middle::ty::{self, TyKind},
    span::symbol,
};
use task_encoder::{
    TaskEncoder,
    TaskEncoderDependencies,
};

/// Takes a Rust `Ty` and returns a Viper `Type`. The returned type is always a
/// domain type. To get specifics such as constructors for the domain, use the
/// full encoding: this is generally the one to use as it also includes the type.
pub struct SnapshotEnc;

#[derive(Clone, Debug)]
pub struct SnapshotEncOutputRef<'vir> {
    pub snapshot: vir::Type<'vir>,
}
impl<'vir> task_encoder::OutputRefAny for SnapshotEncOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct SnapshotEncOutput<'vir> {
    pub base_name: String,
    pub snapshot: vir::Type<'vir>,
    pub specifics: DomainEncSpecifics<'vir>,
}

use super::domain::{DomainEnc, DomainEncSpecifics};

impl TaskEncoder for SnapshotEnc {
    task_encoder::encoder_cache!(SnapshotEnc);

    type TaskDescription<'tcx> = ty::Ty<'tcx>;
    type OutputRef<'vir> = SnapshotEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = SnapshotEncOutput<'vir>;
    type EncodingError = ();

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
        vir::with_vcx(|vcx| {
            // Here we need to normalise the task description.
            // In particular, any concrete type parameter instantiation is replaced
            // with the identity substitutions for the item.
            // For example:
            //     Assuming `struct Foo<T, U> { .. }`,
            //     `Foo<i32, bool>` is normalised to `Foo<T, U>`
            let (ty, args) = match *task_key.kind() {
                TyKind::Adt(adt, args) => {
                    let id = ty::List::identity_for_item(vcx.tcx(), adt.did()).iter()
                        .map(|id| Self::to_placeholder_arg(vcx.tcx(), id));
                    let id = vcx.tcx().mk_args_from_iter(id);
                    let ty = vcx.tcx().mk_ty_from_kind(TyKind::Adt(adt, id));
                    (ty, args.into_iter().flat_map(ty::GenericArg::as_type).collect())
                }
                TyKind::Tuple(tys) => {
                    let new_tys = vcx.tcx().mk_type_list_from_iter((0..tys.len()).map(|index|
                        Self::to_placeholder(vcx.tcx(), Some(index))
                    ));
                    let ty = vcx.tcx().mk_ty_from_kind(TyKind::Tuple(new_tys));
                    (ty, tys.to_vec())
                }
                TyKind::Param(mut param) => {
                    // TODO: remove this hack of using a very large index to
                    // indicate that this is a Viper param.
                    if Self::is_viper_param(param.index) {
                        // We are encoding a previously normalised type
                        // parameter. Stop here.
                        let snapshot = vcx.alloc(vir::TypeData::DomainTypeParam(vir::DomainParamData {
                            name: vir::vir_format!(vcx, "{}", param.name),
                        }));
                        deps.emit_output_ref::<Self>(*task_key, SnapshotEncOutputRef { snapshot });
                        let specifics = DomainEncSpecifics::Param;
                        return Ok((SnapshotEncOutput { base_name: String::new(), snapshot, specifics }, ()));
                    } else {
                        // We want to encode a type parameter for e.g. a generic
                        // method, this will result in an empty domain.
                        param.name = symbol::Symbol::intern(&format!("Param{}", param.index));
                        let ty = vcx.tcx().mk_ty_from_kind(TyKind::Param(param));
                        (ty, Vec::new())
                    }
                }
                TyKind::Array(orig, val) => {
                    let ty = Self::to_placeholder(vcx.tcx(), None);
                    let ty = vcx.tcx().mk_ty_from_kind(TyKind::Array(ty, val));
                    (ty, vec![orig])
                }
                TyKind::Slice(orig) => {
                    let ty = Self::to_placeholder(vcx.tcx(), None);
                    let ty = vcx.tcx().mk_ty_from_kind(TyKind::Slice(ty));
                    (ty, vec![orig])
                }
                TyKind::Ref(r, orig, m) => {
                    let ty = Self::to_placeholder(vcx.tcx(), None);
                    let ty = vcx.tcx().mk_ty_from_kind(TyKind::Ref(r, ty, m));
                    (ty, vec![orig])
                }
                _ => (*task_key, Vec::new()),
            };
            let out = deps.require_ref::<DomainEnc>(ty).unwrap();
            let tys: Vec<_> = args.iter().map(|arg| deps.require_ref::<Self>(*arg).unwrap().snapshot).collect();
            let snapshot = out.domain.apply(vcx, &tys);
            deps.emit_output_ref::<Self>(*task_key, SnapshotEncOutputRef { snapshot });

            let mut names = vec![out.base_name];
            for arg in args {
                let arg = deps.require_local::<Self>(arg).unwrap();
                names.push(arg.base_name);
            }
            // TODO: figure out nicer way to avoid name clashes
            let base_name = names.join("_$_");
            let specifics = deps.require_dep::<DomainEnc>(ty).unwrap();
            Ok((SnapshotEncOutput { base_name, snapshot, specifics }, ()))
        })
    }
}

impl SnapshotEnc {
    pub fn from_viper_param(idx: u32) -> u32 {
        u32::MAX - idx
    }
    fn to_viper_param(idx: u32) -> u32 {
        // Use a very large index to indicate that this is not a Rust param
        // which should be encoded as an empty domain, but that this is a Viper
        // param which should be encoded as a type parameter.
        u32::MAX - idx
    }
    fn is_viper_param(idx: u32) -> bool {
        idx > u32::MAX / 2
    }

    pub fn to_placeholder<'tcx>(tcx: ty::TyCtxt<'tcx>, idx: Option<usize>) -> ty::Ty<'tcx> {
        let name = idx.map(|idx| format!("T{idx}")).unwrap_or_else(|| String::from("T"));
        tcx.mk_ty_from_kind(TyKind::Param(ty::ParamTy {
            index: Self::to_viper_param(idx.unwrap_or_default() as u32),
            name: symbol::Symbol::intern(&name),
        }))
    }
    fn to_placeholder_arg<'tcx>(tcx: ty::TyCtxt<'tcx>, arg: ty::GenericArg<'tcx>) -> ty::GenericArg<'tcx> {
        arg.as_type().map(|ty| {
            let param = DomainEnc::expect_param(ty);
            tcx.mk_ty_from_kind(TyKind::Param(ty::ParamTy {
                index: Self::to_viper_param(param.index),
                name: param.name,
            })).into()
        }).unwrap_or(arg)
    }
}
