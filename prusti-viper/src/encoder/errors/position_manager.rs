// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use vir_crate::polymorphic::Position;
use rustc_hash::FxHashMap;
use prusti_rustc_interface::errors::MultiSpan;
use log::trace;
use prusti_interface::data::ProcedureDefId;

/// Mapping from VIR positions to the source code that generated them.
/// One VIR position can be involved in multiple errors. If an error needs to refer to a special
/// span, that should be done by adding the span to `ErrorCtxt`, not by registering a new span.
#[derive(Clone)]
pub struct PositionManager {
    pos_id_map: FxHashMap<ProcedureDefId, Vec<MultiSpan>>,
}

impl PositionManager {
    pub fn default() -> Self {
        PositionManager {
            pos_id_map: FxHashMap::default(),
        }
    }

    pub fn register_span<T: Into<MultiSpan>>(&mut self, def_id: ProcedureDefId, span: T) -> Position {
        let span = span.into();
        let proc_spans = self.pos_id_map.entry(def_id).or_insert(Vec::new());
        let pos = Self::idx_to_pos(proc_spans.len());
        trace!("Register position id {} for span {:?} in {:?}, ", pos.id(), span, def_id);
        proc_spans.push(span);
        pos
    }

    pub fn duplicate(&mut self, def_id: ProcedureDefId, pos: Position) -> Position {
        assert!(!pos.is_default());
        self.register_span(def_id, self.get_span(def_id, pos).unwrap().clone())
    }

    pub fn get_span(&self, def_id: ProcedureDefId, pos: Position) -> Option<&MultiSpan> {
        let idx = Self::pos_to_idx(pos)?;
        self.pos_id_map.get(&def_id).and_then(|proc_spans| proc_spans.get(idx))
    }

    fn idx_to_pos(idx: usize) -> Position {
        Position::new(idx as u64 + 1)
    }
    fn pos_to_idx(pos: Position) -> Option<usize> {
        if pos.id() == 0 { None }
        else { Some(pos.id() as usize - 1) }
    }
}
