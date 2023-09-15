use prusti_interface::environment::mir_utils::MirPlace;
use prusti_rustc_interface::{
    middle::{mir, mir::visit::Visitor},
    target::abi,
};
use rustc_hash::FxHashSet;

pub fn detect_downcasts<'tcx>(
    body: &mir::Body<'tcx>,
    location: mir::Location,
) -> Vec<(MirPlace<'tcx>, abi::VariantIdx)> {
    let mut collector = DownCastCollector::default();
    collector.visit_location(body, location);
    let mut downcasts: Vec<_> = collector.downcasts.into_iter().collect();
    // Order downcasts starting from the base
    downcasts.sort_unstable_by_key(|(place, _)| (place.local.index(), place.projection.len()));
    downcasts
}

#[derive(Default)]
struct DownCastCollector<'tcx> {
    pub downcasts: FxHashSet<(MirPlace<'tcx>, abi::VariantIdx)>,
}

impl<'tcx> Visitor<'tcx> for DownCastCollector<'tcx> {
    fn visit_projection_elem(
        &mut self,
        place_ref: mir::PlaceRef<'tcx>,
        elem: mir::PlaceElem<'tcx>,
        context: mir::visit::PlaceContext,
        location: mir::Location,
    ) {
        self.super_projection_elem(place_ref, elem, context, location);

        if let mir::PlaceElem::Downcast(_, variant) = elem {
            self.downcasts.insert((
                // FIXME: Store `PlaceRef`, once `visit_projection_elem` will provide that.
                MirPlace {
                    local: place_ref.local,
                    projection: place_ref.projection.to_owned(),
                },
                variant,
            ));
        }
    }
}
