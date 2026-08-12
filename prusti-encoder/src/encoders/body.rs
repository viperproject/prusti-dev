use pcg::pcg::BodyWithBorrowckFacts;
use prusti_interface::environment::{EnvQuery, body::MirBody};
use prusti_rustc_interface::{
    middle::ty,
    span::def_id::{DefId, LocalDefId},
};

use crate::trait_support::is_function_with_body;

/// Whether the body of `def_id` is encoded, rather than only its contract.
/// It is not if the function is trusted (we take its contract on faith), or
/// if it has no body of its own to encode (an external function, or a trait
/// method without a default implementation).
pub fn encodes_body(def_id: DefId) -> bool {
    if crate::encoders::is_function_trusted(def_id) {
        tracing::info!("function {def_id:?} is trusted, not encoding its body");
        return false;
    }
    vir::with_vcx(|vcx| {
        is_function_with_body(vcx.tcx(), def_id) && EnvQuery::new(vcx.tcx()).has_body(def_id)
    })
}

/// The MIR body of `def_id` to encode, or `None` if there is none (see
/// [encodes_body]). The body is the one the compiler produced: as the
/// encoding is generic it is not instantiated, which also keeps the regions
/// that the PCG needs.
pub fn impure_body<'vir>(def_id: DefId) -> Option<MirBody<'vir>> {
    let def_id = local_to_encode(def_id)?;
    vir::with_vcx(|vcx| Some(vcx.body_mut().get_impure_fn_body_identity(def_id)))
}

/// As [impure_body], together with the borrowck facts needed by the PCG.
pub fn impure_body_with_facts<'vir>(def_id: DefId) -> Option<BodyWithBorrowckFacts<'vir>> {
    let def_id = local_to_encode(def_id)?;
    vir::with_vcx(|vcx| Some(vcx.body_mut().get_impure_fn_body_with_facts(def_id)))
}

/// The MIR body of the pure function `def_id`. Only the bodies of functions
/// whose specification marks them pure are preloaded (they must be exported
/// across crates); a local function is pure by inheritance from the trait
/// method it implements, so its body is taken like any other local body.
pub fn pure_body<'vir>(def_id: DefId) -> MirBody<'vir> {
    impure_body(def_id).unwrap_or_else(|| {
        vir::with_vcx(|vcx| {
            let substs = ty::GenericArgs::identity_for_item(vcx.tcx(), def_id);
            vcx.body_mut().get_pure_fn_body(def_id, substs, None)
        })
    })
}

/// The MIR body of the specification `def_id`, taken generically (i.e. with
/// its own parameters, see [instantiated_spec_body] for the exception).
pub fn spec_body<'vir>(def_id: DefId) -> MirBody<'vir> {
    vir::with_vcx(|vcx| {
        let substs = ty::GenericArgs::identity_for_item(vcx.tcx(), def_id);
        vcx.body_mut().get_spec_body(def_id, substs, None)
    })
}

fn local_to_encode(def_id: DefId) -> Option<LocalDefId> {
    encodes_body(def_id).then(|| def_id.as_local()).flatten()
}
