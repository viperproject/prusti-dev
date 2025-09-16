use prusti_rustc_interface::{
    hir::{self, def_id::DefId},
    middle::ty::{self, TyKind},
    span::symbol,
};
use task_encoder::{EncodeFullError, EncodeFullResult, TaskEncoder, TaskEncoderDependencies};


pub struct MostGenericTyEnc;

/// The "most generic" version of a type is one that uses "identity
/// substitutions" for all type parameters. For example, the most generic
/// version of `Vec<u32>` is `Vec<T>`, the most generic version of
/// `Option<Vec<U>>` is `Option<T>`, etc.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct MostGenericTy<'tcx>(ty::Ty<'tcx>);

pub type MostGenericTyEncError = ();

impl TaskEncoder for MostGenericTyEnc {
    task_encoder::encoder_cache!(MostGenericTyEnc);

    type TaskDescription<'vir> = ty::Ty<'vir>;

    type OutputFullLocal<'vir> = (MostGenericTy<'vir>, Vec<ty::Ty<'vir>>);

    type EncodingError = MostGenericTyEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        vir::with_vcx(|vcx| {
            vcx.tcx().erase_regions(*task)
        })
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        vir::with_vcx(|vcx| {
            Ok((Self::extract_type_params(vcx.tcx(), *task_key).ok_or(EncodeFullError::EncodingError((), None))?, ()))
        })
    }
}

impl MostGenericTyEnc {
    pub fn extract_type_params<'tcx>(
        tcx: ty::TyCtxt<'tcx>,
        ty: ty::Ty<'tcx>,
    ) -> Option<(MostGenericTy<'tcx>, Vec<ty::Ty<'tcx>>)> {
        Some(match *ty.kind() {
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
            TyKind::Array(inner, val) => {
                let ty = to_placeholder(tcx, None);
                let ty = tcx.mk_ty_from_kind(TyKind::Array(ty, val));
                (MostGenericTy(ty), vec![inner])
            }
            TyKind::Slice(inner) => {
                let ty = to_placeholder(tcx, None);
                let ty = tcx.mk_ty_from_kind(TyKind::Slice(ty));
                (MostGenericTy(ty), vec![inner])
            }
            TyKind::Ref(_, inner, ty::Mutability::Not) => {
                let ty = to_placeholder(tcx, None);
                let ty = tcx.mk_ty_from_kind(TyKind::Ref(
                    tcx.lifetimes.re_erased,
                    ty,
                    ty::Mutability::Not,
                ));
                (MostGenericTy(ty), vec![inner])
            }
            TyKind::Ref(_, _, ty::Mutability::Mut) => {
                let ty = to_placeholder(tcx, None);
                let ty = tcx.mk_ty_from_kind(TyKind::Ref(
                    tcx.lifetimes.re_erased,
                    ty,
                    ty::Mutability::Mut,
                ));
                (MostGenericTy(ty), vec![]) // vec![inner])
            }
            TyKind::RawPtr(inner, m) => {
                let ty = to_placeholder(tcx, None);
                let ty = tcx.mk_ty_from_kind(TyKind::RawPtr(ty, m));
                (MostGenericTy(ty), vec![inner])
            }
            TyKind::Param(_) => (MostGenericTy(to_placeholder(tcx, None)), Vec::new()),
            TyKind::Closure(_, args) => {
                let args = args.as_closure()
                    .parent_args()
                    .iter()
                    .copied()
                    .filter_map(ty::GenericArg::as_type)
                    .collect();
                (MostGenericTy(ty), args)
            }
            TyKind::Bool
            | TyKind::Char
            | TyKind::Int(_)
            | TyKind::Uint(_)
            | TyKind::Float(_)
            | TyKind::Never
            | TyKind::Str
            | TyKind::FnPtr(..) => (MostGenericTy(ty), Vec::new()),

            // `extern type`s will probably not have generics, but this will be
            // resolved in https://github.com/rust-lang/rust/issues/43467.
            TyKind::Foreign(..) => (MostGenericTy(ty), Vec::new()),

            TyKind::Pat(base_ty, _) => return Self::extract_type_params(tcx, base_ty),

            TyKind::FnDef(..) => return None,
            TyKind::UnsafeBinder(..) => return None,
            TyKind::Dynamic(..) => return None,
            TyKind::Coroutine(..) => return None,
            TyKind::CoroutineClosure(..) => return None,
            TyKind::CoroutineWitness(..) => return None,
            TyKind::Alias(..) => return None,

            kind @ (TyKind::Placeholder(..)
            | TyKind::Error(..)
            | TyKind::Infer(..)
            | TyKind::Bound(..)) => unreachable!("found unexpected type kind {kind:?} (should not appear in Prusti-consumed MIR)"),
        })
    }
}

pub fn get_vir_base_name_kind<'tcx>(kind: &ty::TyKind<'tcx>, vcx: &vir::VirCtxt<'tcx>) -> String {
    match kind {
        TyKind::Bool => String::from("Bool"),
        TyKind::Char => String::from("Char"),
        TyKind::Int(kind) => format!("Int_{}", kind.name_str()),
        TyKind::Uint(kind) => format!("UInt_{}", kind.name_str()),
        TyKind::Float(kind) => format!("Float_{}", kind.name_str()),
        TyKind::Str => String::from("String"),
        TyKind::Adt(adt, _) => vcx.tcx().item_name(adt.did()).to_ident_string(),
        TyKind::Tuple(params) => format!("{}_Tuple", params.len()),
        TyKind::Never => String::from("Never"),
        TyKind::Ref(_, _, ty::Mutability::Not) => String::from("Ref_immutable"),
        TyKind::Ref(_, _, ty::Mutability::Mut) => String::from("Ref_mutable"),
        TyKind::RawPtr(_, ty::Mutability::Not) => String::from("RawPtr_immutable"),
        TyKind::RawPtr(_, ty::Mutability::Mut) => String::from("RawPtr_mutable"),
        TyKind::Param(_) => String::from("Param"),
        TyKind::Closure(def_id, _) => {
            let def_key = vcx.tcx().def_key(def_id);
            match def_key.disambiguated_data.data {
                // Asking for the item_name of a closure triggers an ICE in
                // the compiler, so we give it a name based on its parent.
                hir::definitions::DefPathData::Closure => format!(
                    "{}_Closure_{}",
                    vcx.tcx().item_name(DefId {
                        krate: def_id.krate,
                        index: def_key.parent.unwrap()
                    }),
                    def_key.disambiguated_data.disambiguator,
                ),
                _ => vcx.tcx().item_name(*def_id).to_ident_string(),
            }
        }
        TyKind::FnPtr(..) => String::from("FnPtr"),
        other => unimplemented!("get_vir_base_name for {:?}", other),
    }
}

impl<'tcx: 'vir, 'vir> MostGenericTy<'tcx> {
    pub fn get_vir_domain_ident(
        &self,
        vcx: &'vir vir::VirCtxt<'tcx>,
    ) -> vir::DomainIdn<'vir, vir::Snap> {
        let base_name = self.get_vir_base_name(vcx);
        vir::DomainIdn::new(vir::vir_format_identifier!(vcx, "s_{base_name}"))
    }
}

impl<'tcx> MostGenericTy<'tcx> {
    pub fn get_vir_base_name(&self, vcx: &vir::VirCtxt<'tcx>) -> String {
        get_vir_base_name_kind(self.kind(), vcx)
    }

    pub fn is_generic(&self) -> bool {
        matches!(self.kind(), TyKind::Param(_))
    }

    pub fn kind(&self) -> &'tcx TyKind<'tcx> {
        self.0.kind()
    }

    pub fn param() -> Self {
        vir::with_vcx(|vcx| MostGenericTy(to_placeholder(vcx.tcx(), None)))
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
            TyKind::Array(inner, _) => vec![as_param_ty(*inner)],
            TyKind::Slice(inner) => vec![as_param_ty(*inner)],
            TyKind::Ref(_, inner, ty::Mutability::Not) => vec![as_param_ty(*inner)],
            TyKind::Ref(_, _, ty::Mutability::Mut) => vec![],
            TyKind::RawPtr(inner, _) => vec![as_param_ty(*inner)],
            TyKind::Param(p) => vec![p],
            TyKind::Closure(_, args) => {
                args.as_closure()
                    .parent_args()
                    .iter()
                    .copied()
                    .filter_map(ty::GenericArg::as_type)
                    .map(as_param_ty)
                    .collect()
            }
            TyKind::Bool
            | TyKind::Char
            | TyKind::Float(_)
            | TyKind::Int(_)
            | TyKind::Never
            | TyKind::Uint(_)
            | TyKind::Str
            | TyKind::FnPtr(..) => Vec::new(),
            other => todo!("generics for {:?}", other),
        }
    }

    fn generic_locals<'a, 'vir>(&self, vcx: &'vir vir::VirCtxt<'a>) -> impl Iterator<Item = vir::LocalTyVal<'vir>> + use<'vir, 'tcx, 'a> {
        self.generics()
            .into_iter()
            .map(|ty| vcx.mk_local(
                vcx.alloc_str(ty.name.as_str()),
                vir::TYPE_TYVAL,
            ))
    }

    pub fn generic_decls<'vir>(&self, vcx: &'vir vir::VirCtxt) -> Vec<vir::LocalDeclTyVal<'vir>> {
        self.generic_locals(vcx)
            .map(|local| vcx.mk_local_decl_local(local))
            .collect::<Vec<_>>()
    }

    pub fn generic_exprs<'vir>(&self, vcx: &'vir vir::VirCtxt) -> Vec<vir::ExprTyVal<'vir>> {
        self.generic_locals(vcx)
            .map(|local| vcx.mk_local_ex_local(local))
            .collect::<Vec<_>>()
    }

    pub fn generic_tys<'vir>(&self, vcx: &'vir vir::VirCtxt) -> Vec<vir::TypeTyVal<'vir>> {
        self.generic_locals(vcx)
            .map(|local| local.ty)
            .collect::<Vec<_>>()
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
