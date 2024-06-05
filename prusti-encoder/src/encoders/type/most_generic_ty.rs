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
            TyKind::Generator(def_id, _, _) => vir::vir_format_identifier!(vcx, "Generator_{}", vcx.tcx().def_path_str(def_id)).to_str().to_string(),
            TyKind::GeneratorWitness(_) => String::from("GeneratorWitness"),
            TyKind::RawPtr(ty::TypeAndMut { ty: _, mutbl }) => {
                if mutbl.is_mut() {
                    String::from("RawPtr_mutable")
                } else {
                    String::from("RawPtr_immutable")
                }
            }
            TyKind::FnPtr(_) => String::from("FnPtr"),
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
            TyKind::Generator(_, args, _) => args
                .into_iter()
                .flat_map(ty::GenericArg::as_type)
                .map(as_param_ty)
                .collect(),
            // FIXME: these are only in here to permit encoding async code
            TyKind::RawPtr(ty::TypeAndMut { ty: orig, mutbl: _ }) => vec![as_param_ty(*orig)],
            TyKind::Str
            | TyKind::FnPtr(_)
            | TyKind::GeneratorWitness(_) => Vec::new(),
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
        TyKind::Alias(ty::AliasKind::Opaque, _alias_ty) => {
            let underlying = tcx.expand_opaque_types(ty);
            extract_type_params(tcx, underlying)
        }
        TyKind::Generator(def_id, args, movability) => {
            let id = ty::List::identity_for_item(tcx, def_id).iter();
            let id = tcx.mk_args_from_iter(id);
            let ty = tcx.mk_ty_from_kind(TyKind::Generator(def_id, id, movability));
            (
                MostGenericTy(ty),
                args.into_iter().flat_map(ty::GenericArg::as_type).collect(),
            )
        }
        // FIXME: these are only dummies to permit encoding async code
        TyKind::GeneratorWitness(_) => {
            // we erase generic args inside the witness to avoid encoding
            // the same dummy domain twice
            let dummy_witness_ty = TyKind::GeneratorWitness(ty::Binder::dummy(ty::List::empty()));
            (MostGenericTy(tcx.mk_ty_from_kind(dummy_witness_ty)), Vec::new())
        },
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
        TyKind::RawPtr(ty::TypeAndMut { ty: orig, mutbl }) => {
            let ty = to_placeholder(tcx, None);
            let ty = tcx.mk_ty_from_kind(TyKind::RawPtr(ty::TypeAndMut { ty, mutbl }));
            (MostGenericTy(ty), vec![orig])
        }
        _ => todo!("extract_type_params for {:?}", ty),
    }
}
