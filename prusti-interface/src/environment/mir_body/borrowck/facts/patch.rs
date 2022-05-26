use super::{AllInputFacts, LocationTable, Point, RichLocation};
use crate::environment::mir_body::patch::MirPatch;
use rustc_hash::FxHashMap;
use rustc_middle::mir;

/// FIXME: Currently, this function patches only `borrowck_input_facts.cfg_edge`.
/// It probably should also patch other facts. For example, added drop flag
/// assignment statements may mark some lifetimes as dead and result in premature
/// ending of borrows. Potential example:
/// ```ignore
/// fn test6() {
///     let a = T { f: 4 };
///     let b = T3 { g: a };
///     let mut c = 4;
///     let x = &mut c;
///     if random() {
///         drop(b.g);
///         *x = 5;
///     }
/// }
/// ```
pub fn apply_patch_to_borrowck<'tcx>(
    borrowck_input_facts: &mut AllInputFacts,
    location_table: &mut LocationTable,
    patch: &MirPatch<'tcx>,
    old_body: &mir::Body<'tcx>,
    patched_body: &mir::Body<'tcx>,
) {
    let mut lt_patcher = LocationTablePatcher::new(location_table);

    let mut cfg_edges = FxHashMap::<_, Vec<_>>::default();
    for (from, to) in std::mem::take(&mut borrowck_input_facts.cfg_edge) {
        cfg_edges.entry(from).or_default().push(to);
        cfg_edges.entry(to).or_default();
    }

    let mut block_sizes: FxHashMap<_, _> = old_body
        .basic_blocks()
        .iter_enumerated()
        .map(|(bb, data)| (bb, data.statements.len()))
        .collect();

    // Create cfg_edge facts for the new basic blocks.
    let bb_base = old_body.basic_blocks().len();
    for (offset, block) in patch.new_blocks.iter().enumerate() {
        // +1 is for terminator.
        let mut statement_indices = 0usize..block.statements.len() + 1;
        if let Some(first) = statement_indices.next() {
            cfg_edges.insert(
                lt_patcher.next_start_point(bb_base + offset, first),
                vec![lt_patcher.next_mid_point(bb_base + offset, first)],
            );
        }
        for statement_index in statement_indices {
            cfg_edges.insert(
                lt_patcher.next_start_point(bb_base + offset, statement_index),
                vec![lt_patcher.next_mid_point(bb_base + offset, statement_index)],
            );
            cfg_edges.insert(
                lt_patcher.next_mid_point(bb_base + offset, statement_index - 1),
                vec![lt_patcher.next_start_point(bb_base + offset, statement_index)],
            );
        }
        let mut successor_points = Vec::new();
        for successor in block.terminator().successors() {
            let following_start_point = lt_patcher.start_point(successor.index(), 0);
            successor_points.push(following_start_point);
        }
        cfg_edges.insert(
            lt_patcher.mid_point(bb_base + offset, block.statements.len()),
            successor_points,
        );
        block_sizes.insert((bb_base + offset).into(), block.statements.len());
    }

    // Patch cfg_edge facts for the inserted statements.
    let predecessors = patched_body.predecessors();
    let mut new_statements: Vec<_> = patch
        .new_statements
        .iter()
        .map(|(location, _)| *location)
        .collect();
    new_statements.sort();
    let mut delta = 0;
    let mut last_bb = mir::START_BLOCK;
    let mut predecessors_to_patch = Vec::new();
    for mut loc in new_statements {
        if loc.block != last_bb {
            delta = 0;
            last_bb = loc.block;
        }
        loc.statement_index += delta;

        let old_statement_start_point =
            lt_patcher.start_point(loc.block.index(), loc.statement_index);

        // Shift all points by one statement down.
        lt_patcher.insert_statement_at(loc, &mut block_sizes);

        let statement_start_point = lt_patcher.start_point(loc.block.index(), loc.statement_index);
        let statement_mid_point = lt_patcher.mid_point(loc.block.index(), loc.statement_index);
        let next_statement_start_point =
            lt_patcher.start_point(loc.block.index(), loc.statement_index + 1);
        if loc.statement_index == 0 {
            predecessors_to_patch.push((loc, old_statement_start_point, statement_start_point));
        } else {
            // Insert the statement and patch the links with the previous and following statements.
            let previous_statement_mid_point =
                lt_patcher.mid_point(loc.block.index(), loc.statement_index - 1);
            assert!(cfg_edges
                .insert(previous_statement_mid_point, vec![statement_start_point])
                .is_some());
        }
        assert!(cfg_edges
            .insert(statement_start_point, vec![statement_mid_point])
            .is_none());
        assert!(cfg_edges
            .insert(statement_mid_point, vec![next_statement_start_point])
            .is_none());

        delta += 1;
    }
    for (loc, old_statement_start_point, statement_start_point) in predecessors_to_patch {
        for predecessor in &predecessors[loc.block] {
            eprintln!("predecessor: {:?} loc: {:?}", predecessor, loc);
            let terminator_mid_point = lt_patcher.mid_point(
                predecessor.index(),
                patched_body[*predecessor].statements.len(),
            );
            let mut found = false;
            for target_point in cfg_edges.get_mut(&terminator_mid_point).unwrap() {
                if *target_point == old_statement_start_point {
                    assert!(!found);
                    *target_point = statement_start_point;
                    found = true;
                }
            }

            assert!(
                found,
                "location: {:?}, predecessor: {:?} target_points: {:?} \
                terminator_mid_point: {:?} old_statement_start_point: {:?}",
                loc,
                predecessor,
                cfg_edges[&terminator_mid_point],
                terminator_mid_point,
                old_statement_start_point
            );
        }
    }

    // Patch cfg_edge facts for the replaced terminators.
    for (src, patch) in patch.patch_map.iter_enumerated() {
        if let Some(patch) = patch {
            match patch {
                mir::TerminatorKind::Goto { target } => {
                    assert!(cfg_edges
                        .insert(
                            lt_patcher.mid_point(src.index(), block_sizes[&src]),
                            vec![lt_patcher.start_point(target.index(), 0),]
                        )
                        .is_some());
                }
                mir::TerminatorKind::Drop { target, unwind, .. } => {
                    let mut target_points = vec![lt_patcher.start_point(target.index(), 0)];
                    if let Some(unwind) = unwind {
                        target_points.push(lt_patcher.start_point(unwind.index(), 0));
                    }
                    assert!(cfg_edges
                        .insert(
                            lt_patcher.mid_point(src.index(), block_sizes[&src]),
                            target_points
                        )
                        .is_some());
                }
                _ => unreachable!("patch: {:?}", patch),
            }
        }
    }

    borrowck_input_facts.cfg_edge = cfg_edges
        .into_iter()
        .flat_map(|(from, targets)| targets.into_iter().map(move |target| (from, target)))
        .collect();
}

struct LocationTablePatcher<'a> {
    location_table: &'a mut LocationTable,
    next_point: usize,
}

impl<'a> LocationTablePatcher<'a> {
    fn new(location_table: &'a mut LocationTable) -> Self {
        let next_point = location_table
            .locations
            .keys()
            .max()
            .map(|point| point.index())
            .unwrap_or(1usize)
            + 1;
        Self {
            location_table,
            next_point,
        }
    }

    fn point(&self, location: RichLocation) -> Point {
        self.location_table.points[&location]
    }

    fn start_point(&mut self, block: usize, statement_index: usize) -> Point {
        self.point(RichLocation::Start(mir::Location {
            block: block.into(),
            statement_index,
        }))
    }

    fn mid_point(&mut self, block: usize, statement_index: usize) -> Point {
        self.point(RichLocation::Mid(mir::Location {
            block: block.into(),
            statement_index,
        }))
    }

    fn fresh_point(&mut self) -> Point {
        let point = self.next_point.into();
        self.next_point += 1;
        point
    }

    fn next_point(&mut self, location: RichLocation) -> Point {
        if let Some(point) = self.location_table.points.get(&location) {
            *point
        } else {
            let point = self.fresh_point();
            self.location_table.locations.insert(point, location);
            self.location_table.points.insert(location, point);
            point
        }
    }

    fn next_start_point(&mut self, block: usize, statement_index: usize) -> Point {
        self.next_point(RichLocation::Start(mir::Location {
            block: block.into(),
            statement_index,
        }))
    }

    fn next_mid_point(&mut self, block: usize, statement_index: usize) -> Point {
        self.next_point(RichLocation::Mid(mir::Location {
            block: block.into(),
            statement_index,
        }))
    }

    /// Shift locations of all statements by 1 and insert the provided point at that location.
    fn insert_statement_at(
        &mut self,
        location: mir::Location,
        block_sizes: &mut FxHashMap<mir::BasicBlock, usize>,
    ) {
        // Shift all the statements by one.
        let mut target_statement_index = block_sizes[&location.block] + 1; // +1 for terminator;
        while target_statement_index > location.statement_index {
            let statement_index = target_statement_index - 1;
            let old_start_location = RichLocation::start(location.block, statement_index);
            let old_mid_location = RichLocation::mid(location.block, statement_index);
            let old_start_point = self.location_table.points[&old_start_location];
            let old_mid_point = self.location_table.points[&old_mid_location];
            let start_location = RichLocation::start(location.block, target_statement_index);
            let mid_location = RichLocation::mid(location.block, target_statement_index);
            self.location_table
                .locations
                .insert(old_start_point, start_location);
            self.location_table
                .points
                .insert(start_location, old_start_point);
            self.location_table
                .locations
                .insert(old_mid_point, mid_location);
            self.location_table
                .points
                .insert(mid_location, old_mid_point);
            target_statement_index = statement_index;
        }

        // Insert.
        let start_point = self.fresh_point();
        let mid_point = self.fresh_point();
        let start_location = RichLocation::start(location.block, target_statement_index);
        let mid_location = RichLocation::mid(location.block, target_statement_index);
        self.location_table
            .locations
            .insert(start_point, start_location);
        self.location_table
            .points
            .insert(start_location, start_point);
        self.location_table
            .locations
            .insert(mid_point, mid_location);
        self.location_table.points.insert(mid_location, mid_point);

        // Update the sizes map.
        *block_sizes.get_mut(&location.block).unwrap() += 1;
    }
}
