use super::{AllInputFacts, LocationTable, RichLocation};
use prusti_rustc_interface::{data_structures::graph::WithSuccessors, middle::mir};
use rustc_hash::{FxHashMap, FxHashSet};

/// Validate that the input facts match the body.
pub fn validate<'tcx>(
    borrowck_input_facts: &AllInputFacts,
    location_table: &LocationTable,
    body: &mir::Body<'tcx>,
) {
    assert_eq!(location_table.points.len(), location_table.locations.len());

    let mut cfg_edges = FxHashMap::<_, Vec<_>>::default();
    for (from, to) in borrowck_input_facts.cfg_edge.clone() {
        cfg_edges.entry(from).or_default().push(to);
        cfg_edges.entry(to).or_default();
    }

    let mut seen_points = FxHashSet::default();

    for (block, data) in body.basic_blocks().iter_enumerated() {
        let mut location = mir::Location {
            block,
            statement_index: 0,
        };
        // Check statements.
        while location.statement_index < data.statements.len() {
            let start_point = location_table.location_to_point(RichLocation::Start(location));
            let mid_point = location_table.location_to_point(RichLocation::Mid(location));
            let next_start_point =
                location_table.location_to_point(RichLocation::Start(mir::Location {
                    block: location.block,
                    statement_index: location.statement_index + 1,
                }));
            assert_eq!(cfg_edges[&start_point], [mid_point]);
            assert_eq!(cfg_edges[&mid_point], [next_start_point]);

            seen_points.insert(start_point);
            seen_points.insert(mid_point);
            location.statement_index += 1;
        }

        // Check terminators.
        let start_point = location_table.location_to_point(RichLocation::Start(location));
        let mid_point = location_table.location_to_point(RichLocation::Mid(location));
        assert_eq!(cfg_edges[&start_point], [mid_point]);
        let successor_points = &cfg_edges[&mid_point];
        let successors: Vec<_> = body.basic_blocks.successors(block).collect();
        assert_eq!(
            successors.len(),
            successor_points.len(),
            "block: {:?}",
            block
        );
        for successor in successors {
            let following_start_point =
                location_table.location_to_point(RichLocation::Start(mir::Location {
                    block: successor,
                    statement_index: 0,
                }));
            assert!(
                successor_points.contains(&following_start_point),
                "block: {:?} following_start_point: {:?}",
                block,
                following_start_point
            );
        }
        seen_points.insert(start_point);
        seen_points.insert(mid_point);
    }

    for (from, to) in &borrowck_input_facts.cfg_edge {
        assert!(seen_points.contains(from));
        assert!(seen_points.contains(to));
    }
}
