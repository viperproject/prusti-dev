// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt::Debug;

use vir_crate::polymorphic::Position;
use rustc_hash::FxHashMap;
use prusti_rustc_interface::errors::MultiSpan;
use prusti_interface::data::ProcedureDefId;

/// Mapping from VIR positions to the source code that generated them.
/// One VIR position can be involved in multiple errors. If an error needs to refer to a special
/// span, that should be done by adding the span to `ErrorCtxt`, not by registering a new span.
#[derive(Clone)]
pub struct PositionManager {
    next_pos_id: u64,
    /// The def_id of the procedure that generated the given VIR position.
    pub(crate) def_id: FxHashMap<u64, ProcedureDefId>,
    /// The span of the source code that generated the given VIR position.
    pub(crate) source_span: FxHashMap<u64, MultiSpan>,
}

impl Default for PositionManager {
    fn default() -> Self {
        PositionManager {
            next_pos_id: 1,
            def_id: FxHashMap::default(),
            source_span: FxHashMap::default(),
        }
    }
}

impl PositionManager
{
    #[tracing::instrument(level = "trace", skip(self), ret)]
    pub fn register_span<T: Into<MultiSpan> + Debug>(&mut self, def_id: ProcedureDefId, span: T) -> Position {
        let span = span.into();
        let pos_id = self.next_pos_id;
        self.next_pos_id += 1;
        self.def_id.insert(pos_id, def_id);
        self.source_span.insert(pos_id, span);
        Position::new(pos_id as i32, 0, pos_id)
    }

    pub fn duplicate(&mut self, pos: Position) -> Position {
        assert!(!pos.is_default());
        self.register_span(
            self.get_def_id(pos).unwrap(),
            self.get_span(pos).cloned().unwrap(),
        )
    }

    pub fn get_def_id(&self, pos: Position) -> Option<ProcedureDefId> {
        self.def_id.get(&pos.id()).copied()
    }

    pub fn get_span(&self, pos: Position) -> Option<&MultiSpan> {
        self.source_span.get(&pos.id())
    }
}
