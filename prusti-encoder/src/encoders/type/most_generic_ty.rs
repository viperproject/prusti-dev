use prusti_rustc_interface::{
    hir,
    middle::ty::{self, TyKind},
    span::symbol,
};
use vir::{DomainParamData, NullaryArityAny};
/// The "most generic" version of a type is one that uses "identity
/// substitutions" for all type parameters. For example, the most generic
/// version of `Vec<u32>` is `Vec<T>`, the most generic version of
/// `Option<Vec<U>>` is `Option<T>`, etc.
///
/// To construct an instance, use [`extract_type_params`].
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct MostGenericTy<'tcx>(ty::Ty<'tcx>);

impl<'tcx: 'vir, 'vir> MostGenericTy<'tcx> {
    pub fn get_vir_domain_ident(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
    ) -> vir::DomainIdent<'vir, NullaryArityAny<'vir, DomainParamData<'vir>>> {
        let base_name = self.get_vir_base_name(vcx);
        vir::DomainIdent::nullary(vir::vir_format_identifier!(vcx, "s_{base_name}"))
    }
}

impl<'tcx> MostGenericTy<'tcx> {
    pub fn get_vir_base_name(&self, vcx: &vir::VirCtxt<'tcx>) -> String {
        match self.kind() {
            TyKind::Bool => String::from("Bool"),
            TyKind::Char => String::from("Char"),
            TyKind::Int(kind) => format!("Int_{}", kind.name_str()),
            TyKind::Uint(kind) => format!("UInt_{}", kind.name_str()),
            TyKind::Float(kind) => format!("Float_{}", kind.name_str()),
            TyKind::Str => String::from("String"),
            TyKind::Adt(adt, _) => vcx.tcx().item_name(adt.did()).to_ident_string(),
            TyKind::Tuple(params) => format!("{}_Tuple", params.len()),
            TyKind::Never => String::from("Never"),
            TyKind::Ref(_, _, m) => {
                if m.is_mut() {
                    String::from("Ref_mutable")
                } else {
                    String::from("Ref_immutable")
                }
            },
            TyKind::Param(_) => String::from("Param"),
            // TODO: this is to avoid name clashes between the identical generator domains
            // but we should find a better way to do this
            TyKind::Generator(def_id, _, _) =>
                vir::vir_format_identifier!(vcx, "Generator_{}", vcx.tcx().def_path_str(def_id)).to_str().to_string(),
            TyKind::GeneratorWitness(_) => String::from("GeneratorWitness"),
            TyKind::RawPtr(ty::TypeAndMut { ty: _, mutbl }) => {
                if mutbl.is_mut() {
                    String::from("RawPtr_mutable")
                } else {
                    String::from("RawPtr_immutable")
                }
            }
            TyKind::FnPtr(_) => String::from("FnPtr"),
            TyKind::Closure(def_id, _) =>
                vir::vir_format_identifier!(vcx, "Closure_{}", vcx.tcx().def_path_str(def_id)).to_str().to_string(),
            other => unimplemented!("get_domain_base_name for {:?}", other),
        }
    }

    pub fn is_generic(&self) -> bool {
        matches!(self.kind(), TyKind::Param(_))
    }

    pub fn kind(&self) -> &TyKind<'tcx> {
        self.0.kind()
    }

    pub fn tuple(arity: usize) -> Self {
        assert!(arity != 1);
        let tuple = vir::with_vcx(|vcx| {
            let new_tys = vcx.tcx().mk_type_list_from_iter(
                (0..arity).map(|index| to_placeholder(vcx.tcx(), Some(index))),
            );
            vcx.tcx().mk_ty_from_kind(ty::TyKind::Tuple(new_tys))
        });
        MostGenericTy(tuple)
    }

    pub fn ty(&self) -> ty::Ty<'tcx> {
        self.0
    }

    pub fn generics(&self) -> Vec<&'tcx ty::ParamTy> {
        let as_param_ty = |ty: ty::Ty<'tcx>| match ty.kind() {
            TyKind::Param(p) => p,
            _ => unreachable!(),
        };
        match self.kind() {
            TyKind::Adt(_, args) => args
                .into_iter()
                .flat_map(ty::GenericArg::as_type)
                .map(as_param_ty)
                .collect(),
            TyKind::Tuple(tys) => tys.iter().map(as_param_ty).collect::<Vec<_>>(),
            TyKind::Array(orig, _) => vec![as_param_ty(*orig)],
            TyKind::Slice(orig) => vec![as_param_ty(*orig)],
            TyKind::Ref(_, orig, _) => vec![as_param_ty(*orig)],
            TyKind::Bool
            | TyKind::Char
            | TyKind::Float(_)
            | TyKind::Int(_)
            | TyKind::Never
            | TyKind::Param(_)
            | TyKind::Uint(_) => Vec::new(),
            // NOTE: for now this is only for generators originating from async items
            TyKind::Generator(_, args, _) => args
                .as_generator()
                .parent_args()
                .into_iter()
                .flat_map(|arg| arg.as_type())
                .map(as_param_ty)
                .collect(),
            // FIXME: these are only in here to permit encoding async code
            TyKind::RawPtr(_)
            | TyKind::Str
            | TyKind::FnPtr(_)
            | TyKind::GeneratorWitness(_)
            | TyKind::Closure(..)=> Vec::new(),
            other => todo!("generics for {:?}", other),
        }
    }
}

impl<'tcx> From<MostGenericTy<'tcx>> for ty::Ty<'tcx> {
    fn from(value: MostGenericTy<'tcx>) -> Self {
        value.0
    }
}

fn to_placeholder(tcx: ty::TyCtxt<'_>, idx: Option<usize>) -> ty::Ty<'_> {
    let name = idx
        .map(|idx| format!("T{idx}"))
        .unwrap_or_else(|| String::from("T"));
    tcx.mk_ty_from_kind(TyKind::Param(ty::ParamTy {
        index: idx.unwrap_or_default() as u32,
        name: symbol::Symbol::intern(&name),
    }))
}

pub fn extract_type_params<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
) -> (MostGenericTy<'tcx>, Vec<ty::Ty<'tcx>>) {
    match *ty.kind() {
        TyKind::Adt(adt, args) => {
            let id = ty::List::identity_for_item(tcx, adt.did()).iter();
            let id = tcx.mk_args_from_iter(id);
            let ty = tcx.mk_ty_from_kind(TyKind::Adt(adt, id));
            (
                MostGenericTy(ty),
                args.into_iter().flat_map(ty::GenericArg::as_type).collect(),
            )
        }
        TyKind::Tuple(tys) => {
            let new_tys = tcx.mk_type_list_from_iter(
                (0..tys.len()).map(|index| to_placeholder(tcx, Some(index))),
            );
            let ty = tcx.mk_ty_from_kind(TyKind::Tuple(new_tys));
            (MostGenericTy(ty), tys.to_vec())
        }
        TyKind::Array(orig, val) => {
            let ty = to_placeholder(tcx, None);
            let ty = tcx.mk_ty_from_kind(TyKind::Array(ty, val));
            (MostGenericTy(ty), vec![orig])
        }
        TyKind::Slice(orig) => {
            let ty = to_placeholder(tcx, None);
            let ty = tcx.mk_ty_from_kind(TyKind::Slice(ty));
            (MostGenericTy(ty), vec![orig])
        }
        TyKind::Ref(_, orig, m) => {
            let ty = to_placeholder(tcx, None);
            let ty = tcx.mk_ty_from_kind(TyKind::Ref(tcx.lifetimes.re_erased, ty, m));
            (MostGenericTy(ty), vec![orig])
        }
        TyKind::Param(_) => (MostGenericTy(to_placeholder(tcx, None)), Vec::new()),
        TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) | TyKind::Never | TyKind::Str => {
            (MostGenericTy(ty), Vec::new())
        }
        // for now, we replace OTAs by their underlying type in order to ensure that OTAs to async
        // generators are correctly encoded to the same viper type as the generator
        TyKind::Alias(ty::AliasKind::Opaque, _alias_ty) => {
            let underlying = tcx.expand_opaque_types(ty);
            extract_type_params(tcx, underlying)
        }
        TyKind::Generator(def_id, args, movability) if tcx.generator_is_async(def_id) => {
            let args = args.as_generator();
            // the only generic arguments we need to include are the parent arguments,
            // i.e. those present in the async fn (or its outer scope)
            // the other generic arguments arise due to the future's representation as a
            // generator with <resume_ty>, <yield_ty>, <return_ty>, <witness>,
            // and the tupled upvar-ty, all of which are fixed for a given future
            // (or even all futures)
            let parent_args = args
                .parent_args()
                .into_iter()
                .flat_map(|arg| ty::GenericArg::as_type(*arg))
                .collect::<Vec<_>>();
            // we use `List::identity_for_item` to get generic parameters with correct names,
            // as creating placeholders ourselves might result in misnaming parameters
            // that are used in the upvars (attempting to recreate the names from the parent-args
            // also doesn't always work, since they might already be substituted in the parent-args)
            // the parent generic parameters are now contained in the front of the result
            // obtained from `List::identity_for_item`
            // TODO: verify that this is stable
            {
                // sanity-check: number of generic arguments (and type params among them) matches
                let id = ty::List::identity_for_item(tcx, def_id);
                assert_eq!(id.len(), args.parent_args().len() + 5);
                let id = id.into_iter().flat_map(ty::GenericArg::as_type).collect::<Vec<_>>();
                assert_eq!(id.len(), parent_args.len() + 5);
                // TODO: should we check that those afterwards are actually called <resume_ty> and so on?
            }
            let parent_id: Vec<ty::GenericArg> = ty::List::identity_for_item(tcx, def_id)
                .into_iter()
                .flat_map(ty::GenericArg::as_type)
                .take(parent_args.len())
                .map(|arg| arg.into())
                .collect();
            // we also use a dummy witness type to avoid encoding the same generator twice,
            // as the witness type appears once with the generator and once with the OTA to it
            let dummy_witness = tcx.mk_ty_from_kind(
                ty::TyKind::GeneratorWitness(ty::Binder::dummy(ty::List::empty()))
            );
            // note that the upvar types given in the generic arguments might already contain
            // substitutions for some of the async item's type parameters, so we use the `TyCtxt`
            // to obtain the generator's type without any substitutions
            let generic_upvars_ty = {
                let gen_ty = tcx.type_of(def_id).skip_binder();
                let TyKind::Generator(_, args, _) = gen_ty.kind() else {
                    panic!("TyCtxt::type_of returned non-generator type for generator DefId");
                };
                args.as_generator().tupled_upvars_ty()
            };
            let id_parts = ty::GeneratorArgsParts {
                parent_args: tcx.mk_args(&parent_id),
                resume_ty: args.resume_ty(),
                yield_ty: args.yield_ty(),
                return_ty: args.return_ty(),
                witness: dummy_witness,
                tupled_upvars_ty: generic_upvars_ty,
            };
            let id_args = ty::GeneratorArgs::new(tcx, id_parts);
            let ty = tcx.mk_ty_from_kind(
                TyKind::Generator(def_id, id_args.args, movability)
            );
            (MostGenericTy(ty), parent_args)
        }
        // FIXME: these are only dummies to permit encoding async code
        TyKind::GeneratorWitness(_) => {
            // we erase generic args inside the witness to avoid encoding
            // the same dummy domain twice
            let dummy_witness_ty = TyKind::GeneratorWitness(ty::Binder::dummy(ty::List::empty()));
            (MostGenericTy(tcx.mk_ty_from_kind(dummy_witness_ty)), Vec::new())
        },
        // FIXME: these are only dummies to permit encoding async code
        TyKind::FnPtr(binder) => {
            // we erase the signature to avoid encoding
            // the same dummy domain twice
            let sig = binder.skip_binder();
            let unit_ty = tcx.mk_ty_from_kind(TyKind::Tuple(ty::List::empty()));
            let dummy_sig = ty::Binder::dummy(ty::FnSig {
                inputs_and_output: tcx.mk_type_list(&[unit_ty]),
                unsafety: hir::Unsafety::Normal,
                ..sig
            });
            let ty = tcx.mk_ty_from_kind(TyKind::FnPtr(dummy_sig));
            (MostGenericTy(ty), Vec::new())
        }
        // FIXME: these are only dummies to permit encoding async code
        TyKind::RawPtr(ty::TypeAndMut { ty: orig, mutbl }) => {
            let ty = to_placeholder(tcx, None);
            let ty = tcx.mk_ty_from_kind(TyKind::RawPtr(ty::TypeAndMut { ty, mutbl }));
            (MostGenericTy(ty), Vec::new())
            // (MostGenericTy(ty), vec![orig])
        }
        // FIXME: for now, we encode closures like simple wrappers around their upvars in order to
        // use them for on-exit/on-entry conditions in async code
        TyKind::Closure(def_id, args) => {
            // analogous to generator
            let args = args.as_closure();
            let parent_args = args
                .parent_args()
                .into_iter()
                .flat_map(|arg| arg.as_type())
                .collect::<Vec<_>>();
            // sanity-checks
            let id_args = ty::List::identity_for_item(tcx, def_id);
            {
                assert_eq!(id_args.len(), args.parent_args().len() + 3);
                let id = id_args.into_iter().flat_map(ty::GenericArg::as_type).collect::<Vec<_>>();
                assert_eq!(id.len(), parent_args.len() + 3);
            }
            let parent_id: Vec<ty::GenericArg> = id_args
                .into_iter()
                .flat_map(ty::GenericArg::as_type)
                .take(parent_args.len())
                .map(|arg| arg.into())
                .collect();
            let most_generic_args = {
                let closure_ty = tcx.type_of(def_id).skip_binder();
                let TyKind::Closure(_, args) = closure_ty.kind() else {
                    panic!("TyCtxt::type_of returned non-closure type for closure DefId")
                };
                args.as_closure()
            };
            let id_parts = ty::ClosureArgsParts {
                parent_args: tcx.mk_args(&parent_id),
                closure_kind_ty: most_generic_args.kind_ty(),
                closure_sig_as_fn_ptr_ty: most_generic_args.sig_as_fn_ptr_ty(),
                tupled_upvars_ty: most_generic_args.tupled_upvars_ty(),
            };
            let id_args = ty::ClosureArgs::new(tcx, id_parts);
            let ty = tcx.mk_ty_from_kind(
                TyKind::Closure(def_id, id_args.args)
            );
            (MostGenericTy(ty), parent_args)
        }
        _ => todo!("extract_type_params for {:?}", ty),
    }
}
