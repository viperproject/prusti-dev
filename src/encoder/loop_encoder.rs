// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::HashMap;
use rustc::mir;
use prusti_interface::environment::{
    BasicBlockIndex, PlaceAccess, PlaceAccessKind, ProcedureLoops};

pub struct LoopEncoder<'tcx> {
    pub loop_info: ProcedureLoops,
    /// Places that are accessed in each loop. The index of the loop
    /// head basic block is used as a key.
    pub accessed_places: HashMap<BasicBlockIndex, Vec<PlaceAccess<'tcx>>>,
}

/// Struct that defines permissions used in a loop invariant.
pub struct LoopInvariant<'tcx> {
    /// A set of places for which we need to provide read permissions in
    /// the loop invariant. If a place `p` is in `read_places`, then
    /// `acc(T(p), rd)` is added to the loop invariant.
    read_places: Vec<mir::Place<'tcx>>,
    /// A set of places for which we need to provide write permissions in
    /// the loop invariant. If a place `p` is in `write_places`, then
    /// `acc(T(p), write)` is added to the loop invariant.
    written_places: Vec<mir::Place<'tcx>>,
    /// A set of paths for which we need to provide read permissions in the
    /// loop invariant. For example, if a path `x.f.g` is in
    /// `read_access_paths`, then ``acc(x.f, rd) && acc(x.f.g, rd)`` is
    /// added to the loop invariant.
    read_access_paths: Vec<mir::Place<'tcx>>,
    /// A set of paths for which we need to provide write permissions in the
    /// loop invariant. For example, if a path `x.f.g` is in
    /// `write_access_paths`, then ``acc(x.f, write) && acc(x.f.g, write)``
    /// is added to the loop invariant.
    write_access_paths: Vec<mir::Place<'tcx>>,
}

impl<'tcx> LoopEncoder<'tcx> {

    pub fn new<'a>(mir: &'a mir::Mir<'tcx>) -> LoopEncoder<'tcx>
        where 'tcx: 'a
    {
        debug!("LoopEncoder constructor");

        let loop_info = ProcedureLoops::new(mir);
        let mut accessed_places = HashMap::new();
        for &loop_head in loop_info.loop_heads.iter() {
            let accesses = loop_info.compute_used_paths(loop_head, mir);
            accessed_places.insert(loop_head, accesses);
        }
        LoopEncoder {
            loop_info: loop_info,
            accessed_places: accessed_places,
        }
    }

    /// Is the given basic block a loop head?
    pub fn is_loop_head(&self, basic_block: &BasicBlockIndex) -> bool {
        self.loop_info.loop_heads.contains(basic_block)
    }

    /// Check if the place `potential_prefix` is a prefix of `place`. For example:
    ///
    /// +   `is_prefix(x.f, x.f) == true`
    /// +   `is_prefix(x.f.g, x.f) == true`
    /// +   `is_prefix(x.f, x.f.g) == false`
    fn is_prefix(&self, place: &mir::Place<'tcx>, potential_prefix: &mir::Place<'tcx>) -> bool {
        if place == potential_prefix {
            true
        } else {
            match place {
                mir::Place::Local(_) => false,
                mir::Place::Projection(box mir::Projection { base, ..  }) =>
                    self.is_prefix(base, potential_prefix),
                _ => unimplemented!(),
            }
        }
    }

    /// Remove all places from `places` whose prefix is already in `places`.
    fn deduplicate(&self, places: Vec<mir::Place<'tcx>>) -> Vec<mir::Place<'tcx>> {
        let mut filtered_places = Vec::new();
        for place in places.iter() {
            let has_prefix = places
                .iter()
                .any(|prefix| {
                    place != prefix &&
                    self.is_prefix(place, prefix)
                });
            if !has_prefix && !filtered_places.contains(place) {
                filtered_places.push(place.clone());
            }
        }
        filtered_places
    }

    /// To achieve good performance, the Rust compiler uses bitsets
    /// to represent the analysis state. This design decision has two
    /// interesting consequences. First, it can happen that a variable
    /// `x` is marked as initialized while its field `x.f` is marked as
    /// uninitialized. Second, the flow analysis tracks only the places
    /// (`x`, `x.f.g.h`, etc.) that the later Rust compiler passes care
    /// about. As a result, it can happen that the status of some places
    /// at a specific program point is not explicitly available and we
    /// need to compute it (seems that it is always possible to do that).
    ///
    /// Computation algorithm:
    ///
    /// 1.  `written_places := self.accessed_places.filter(kind in Store, Move, MutableBorrow)`
    /// 2.  Deduplicate `written_places` by removing all places whose prefix
    ///     is already in `written_places`.
    /// 3.  Remove all places from `written_places` to which we might not have
    ///     permissions at the loop head (repeat until a fix-point):
    ///
    ///     1.  Remove all places `p` that are mentioned in `maybe_uninit`.
    ///     2.  For each place `p` that is a prefix of some place in
    ///         `maybe_uninit`:
    ///
    ///         1.  Remove it from `written_places`.
    ///         2.  Add all places that are accessible via `p` fields to
    ///             `written_places` and `write_access_paths`.
    ///
    /// 4.  `read_places := self.accessed_places.filter(kind in Copy, SharedBorrow)`
    /// 5.  Deduplicate `read_places`.
    /// 6.  Remove all places from `read_places` to which we might not have
    ///     permissions at the loop head or we already require write
    ///     permissions (repeat until a fix-point):
    ///
    ///     1.  Remove all places `p` that are mentioned in `maybe_uninit`,
    ///         `written_places`, or `write_access_paths`.
    ///     2.  For each place `p` that is a prefix of some place in
    ///         `maybe_uninit`, `written_places`, or `write_access_paths`:
    ///
    ///         1.  Remove it from `read_places`.
    ///         2.  Add all places that are accessible via `p` fields to
    ///             `read_places` and `read_access_paths`.
    ///
    /// 8.  Add all prefixes of all places in `read_places`,
    ///     `written_places`, and `write_access_paths` to
    ///     `read_access_paths`.
    /// 9.  Remove all places from `read_access_paths` that are already in
    ///     `read_places`, `written_places`, or `write_access_paths`.
    pub fn compute_loop_invariant(&self, loop_head: BasicBlockIndex,
                                  //dataflow_info: &mut DataflowInfo
                                  ) -> LoopInvariant<'tcx> {
        let location = mir::Location { block: loop_head, statement_index: 0 };

        let written_places: Vec<_> = self.accessed_places[&loop_head]
            .iter()
            .filter(|access| {
                match access.kind {
                    PlaceAccessKind::Store |
                    PlaceAccessKind::Move |
                    PlaceAccessKind::MutableBorrow => true,
                    PlaceAccessKind::Copy |
                    PlaceAccessKind::SharedBorrow => false,
                }
            })
            .map(|access| {access.place.clone()})
            .collect();
        debug!("written_places1 = {:?}", written_places);
        let written_places = self.deduplicate(written_places);
        debug!("written_places2 = {:?}", written_places);
        let mut written_places = written_places;
        let mut changes = true;
        //let maybe_uninit = dataflow_info.get_maybe_uninit_at(location);
        while changes {
            changes = false;
            // TODO: Finish the implementation based on the description
            // of the algorithm.
        }

        unimplemented!();
    }

}
