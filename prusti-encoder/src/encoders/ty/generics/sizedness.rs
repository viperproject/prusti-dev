use prusti_rustc_interface::span::DUMMY_SP;
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, vir_format_identifier};

use crate::encoders::ty::{
    RustTy, RustTyDecomposition, RustTySizedness,
    generics::{GenericParamsEnc, r#trait::TraitEnc},
    lifted::TyConstructorEnc,
};

/// Encodes a type constructor's facts about the sizedness traits `Sized` and
/// `MetaSized` (`PointeeSized` holds of every type, and bounds on it are
/// skipped, see `TraitImplEnc::context_bounds`). These are implemented by
/// the compiler rather than by impls, so where an ordinary trait's
/// `impl_fun` is established by its impls' conditions, these are
/// established by the constructors, each with an axiom triggered on the
/// application at the constructor:
///
/// ```text
/// axiom { Sized_impl(s_Char_type()) }
/// axiom { forall T :: {Sized_impl(s_W_type(T))} Sized_impl(T) ==> Sized_impl(s_W_type(T)) }
/// ```
///
/// A constructor that does not implement a trait (e.g. `str` for `Sized`)
/// has no axiom for it, which leaves it open rather than false.
pub struct SizednessEnc;

impl TaskEncoder for SizednessEnc {
    task_encoder::encoder_cache!(SizednessEnc);
    const ENCODER_NAME: &'static str = "sizedness encoder";

    type TaskDescription<'vir> = RustTy<'vir>;
    type OutputFullLocal<'vir> = vir::Domain<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        vir::with_vcx(|vcx| {
            let lang_items = vcx.tcx().lang_items();
            // For each trait, `None` if the constructor does not implement
            // it, otherwise the type it is conditional on (if any).
            let (sized, meta_sized) = match task_key.sizedness {
                RustTySizedness::None => unreachable!(),
                RustTySizedness::Sized {
                    sized_if,
                    meta_sized_if,
                } => (Some(sized_if), Some(meta_sized_if)),
                RustTySizedness::MetaSized => (None, Some(None)),
                RustTySizedness::PointeeSized => (None, None),
            };
            let facts = [
                ("Sized", lang_items.sized_trait(), sized),
                ("MetaSized", lang_items.meta_sized_trait(), meta_sized),
            ];

            let params = deps.require_dep::<GenericParamsEnc>(task_key.params)?;
            let constructor = deps.require_ref::<TyConstructorEnc>(*task_key)?;
            let ty = constructor.ty_constructor.call()(params.ty_exprs(), params.const_exprs());
            let base_name = task_key.name();

            let mut axioms = Vec::new();
            for (trait_name, trait_did, fact) in facts {
                let (Some(trait_did), Some(condition)) = (trait_did, fact) else {
                    continue;
                };
                let impl_fun = deps.require_ref::<TraitEnc>(trait_did)?.impl_fun;
                let implemented = impl_fun(&[ty], &[]);
                let body = match condition {
                    None => implemented,
                    Some(tail) => {
                        let tail = RustTyDecomposition::from_ty(tail, task_key.params);
                        let tail_implemented = impl_fun(&[params.ty_expr(deps, tail)?], &[]);
                        vir::expr! { (tail_implemented) ==> (implemented) }
                    }
                };
                let decls = params.ty_decls().iter().map(|decl| decl.upcast_ty());
                let decls = decls.chain(params.const_decls().iter().map(|decl| decl.upcast_ty()));
                axioms.push(vcx.mk_domain_axiom(
                    vir_format_identifier!(vcx, "s_{base_name}_{trait_name}"),
                    vcx.mk_forall_expr(
                        vcx.alloc_slice(&decls.collect::<Vec<vir::LocalDeclDyn>>()),
                        vcx.alloc_slice(&[vcx.mk_trigger(&[implemented])]),
                        body,
                    ),
                ));
            }

            let domain = vcx.mk_domain(
                vir_format_identifier!(vcx, "sizedness_{base_name}"),
                &[],
                vcx.alloc_slice(&axioms),
                &[],
                None,
            );
            Ok((domain, ()))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for domain in Self::all_outputs_local_no_errors(program) {
            program.add_domain(domain);
        }
    }
}

impl SizednessEnc {
    /// Encodes the facts of a type constructor. Called for every constructor
    /// `TyConstructorEnc` encodes.
    pub fn require(constructor: RustTy<'_>) {
        if !matches!(constructor.sizedness, RustTySizedness::None) {
            let _ = Self::encode(constructor, false, DUMMY_SP);
        }
    }
}
