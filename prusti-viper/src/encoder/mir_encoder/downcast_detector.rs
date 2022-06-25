use prusti_rustc_interface::middle::mir;
use prusti_rustc_interface::target::abi;
use prusti_rustc_interface::middle::mir::visit::Visitor;
use prusti_interface::environment::mir_utils::MirPlace;
use rustc_hash::{FxHashSet};

pub fn detect_downcasts<'tcx>(body: &mir::Body<'tcx>, location: mir::Location)
    -> Vec<(MirPlace<'tcx>, abi::VariantIdx)>
{
    let mut collector = DownCastCollector::default();
    collector.visit_location(body, location);
    let mut downcasts: Vec<_> = collector.downcasts.into_iter().collect();
    // Order downcasts starting from the base
    downcasts.sort_by_key(|(place, _)| (place.local.index(), place.projection.len()));
    downcasts
}

#[derive(Default)]
struct DownCastCollector<'tcx> {
    pub downcasts: FxHashSet<(MirPlace<'tcx>, abi::VariantIdx)>
}

impl<'tcx> Visitor<'tcx> for DownCastCollector<'tcx> {
    fn visit_projection_elem(
        &mut self,
        local: mir::Local,
        proj_base: &[mir::PlaceElem<'tcx>],
        elem: mir::PlaceElem<'tcx>,
        context: mir::visit::PlaceContext,
        location: mir::Location,
    ) {
        self.super_projection_elem(local, proj_base, elem, context, location);

        if let mir::PlaceElem::Downcast(_, variant) = elem {
            self.downcasts.insert(
                (
                    // FIXME: Store `PlaceRef`, once `visit_projection_elem` will provide that.
                    MirPlace {
                        local,
                        projection: proj_base.to_owned(),
                    },
                    variant,
                )
            );
        }
    }
}
