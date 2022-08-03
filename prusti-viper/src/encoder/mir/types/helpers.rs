use crate::encoder::utils::{range_extract, PlusOne};

use prusti_rustc_interface::{
    middle::{ty, ty::layout::IntegerExt},
    target::abi::Integer,
};

use vir_crate::{
    high as vir_high,
    polymorphic::{self as vir},
};

/// Compute the values that a discriminant can take.
pub(crate) fn compute_discriminant_values<'tcx>(
    adt_def: ty::AdtDef<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
) -> Vec<i128> {
    let mut discr_values: Vec<i128> = vec![];
    let size = ty::tls::with(|tcx| Integer::from_attr(&tcx, adt_def.repr().discr_type()).size());
    for (_variant_idx, discr) in adt_def.discriminants(tcx) {
        // Sign extend the raw representation to be an i128, to handle *signed* discriminants.
        // See also: https://github.com/rust-lang/rust/blob/b7ebc6b0c1ba3c27ebb17c0b496ece778ef11e18/compiler/rustc_middle/src/ty/util.rs#L35-L45
        discr_values.push(size.sign_extend(discr.val) as i128);
    }
    discr_values
}

/// Encode a disjunction that lists all possible discrimintant values.
pub(super) fn compute_discriminant_ranges<'tcx>(
    adt_def: ty::AdtDef<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
) -> Vec<vir_high::DiscriminantRange> {
    let discr_values = compute_discriminant_values(adt_def, tcx);
    range_extract(discr_values)
}

/// Encode a disjunction that lists all possible discrimintant values.
///
/// FIXME: Remove this code duplication once snapshots are refactored.
pub(crate) fn compute_discriminant_bounds<'tcx>(
    adt_def: ty::AdtDef<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
    discriminant_loc: &vir::Expr,
) -> vir::Expr {
    /// Try to produce the minimal disjunction.
    fn build_discr_range_expr<T: Ord + PartialEq + Eq + Copy + Into<vir::Expr> + PlusOne>(
        discriminant_loc: &vir::Expr,
        discr_values: Vec<T>,
    ) -> vir::Expr {
        if discr_values.is_empty() {
            // A `false` here is unsound. See issues #38 and #158.
            return true.into();
        }
        use vir_crate::polymorphic::ExprIterator;
        range_extract(discr_values)
            .into_iter()
            .map(|(from, to)| {
                if from == to {
                    vir::Expr::eq_cmp(discriminant_loc.clone(), from.into())
                } else {
                    vir::Expr::and(
                        vir::Expr::le_cmp(from.into(), discriminant_loc.clone()),
                        vir::Expr::le_cmp(discriminant_loc.clone(), to.into()),
                    )
                }
            })
            .disjoin()
    }

    // Handle *signed* discriminats
    let discr_values = compute_discriminant_values(adt_def, tcx);
    build_discr_range_expr(discriminant_loc, discr_values)
}
