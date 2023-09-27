// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt::Debug;

use log::debug;
use prusti_interface::data::ProcedureDefId;
use prusti_rustc_interface::{errors::MultiSpan, span::source_map::SourceMap};
use rustc_hash::FxHashMap;
use vir_crate::polymorphic::Position;

/// Mapping from VIR positions to the source code that generated them.
/// One VIR position can be involved in multiple errors. If an error needs to refer to a special
/// span, that should be done by adding the span to `ErrorCtxt`, not by registering a new span.
#[derive(Clone)]
pub struct PositionManager<'tcx> {
    codemap: &'tcx SourceMap,
    next_pos_id: u64,
    /// The def_id of the procedure that generated the given VIR position.
    pub(crate) def_id: FxHashMap<u64, ProcedureDefId>,
    /// The span of the source code that generated the given VIR position.
    pub(crate) source_span: FxHashMap<u64, MultiSpan>,
}

impl<'tcx> PositionManager<'tcx> {
    pub fn new(codemap: &'tcx SourceMap) -> Self {
        PositionManager {
            codemap,
            next_pos_id: 1,
            def_id: FxHashMap::default(),
            source_span: FxHashMap::default(),
        }
    }

    /// Registers a new span and returns the corresponding VIR position.
    /// The line and column of the VIR position correspond to the start of the given span.
    #[tracing::instrument(level = "trace", skip(self), ret)]
    pub fn register_span<T: Into<MultiSpan> + Debug>(
        &mut self,
        def_id: ProcedureDefId,
        span: T,
    ) -> Position {
        let span = span.into();
        let pos_id = self.next_pos_id;
        self.next_pos_id += 1;

        let pos = if let Some(primary_span) = span.primary_span() {
            let lines_info_res = self.codemap.span_to_lines(primary_span.source_callsite());
            match lines_info_res {
                Ok(lines_info) => {
                    if let Some(first_line_info) = lines_info.lines.get(0) {
                        let line = first_line_info.line_index as i32 + 1;
                        let column = first_line_info.start_col.0 as i32 + 1;
                        Position::new(line, column, pos_id)
                    } else {
                        debug!("Primary span of position id {} has no lines", pos_id);
                        Position::new(0, 0, pos_id)
                    }
                }
                Err(e) => {
                    debug!(
                        "Error converting primary span of position id {} to lines: {:?}",
                        pos_id, e
                    );
                    Position::new(0, 0, pos_id)
                }
            }
        } else {
            debug!("Position id {} has no primary span", pos_id);
            Position::new(0, 0, pos_id)
        };

        self.def_id.insert(pos_id, def_id);
        self.source_span.insert(pos_id, span);
        pos
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
