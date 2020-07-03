// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc::hir;
use rustc::hir::intravisit::{self, NestedVisitorMap, Visitor};
use rustc::ty::TyCtxt;
use syntax::ast::NodeId;

pub fn contains_unsafe(tcx: TyCtxt, node_id: NodeId) -> bool {
    let body_id = tcx.hir.body_owned_by(node_id);
    let body = tcx.hir.body(body_id);
    let mut visitor = UnsafetyDetector {
        contains_unsafe: false,
    };
    visitor.visit_body(&body);
    visitor.contains_unsafe
}

struct UnsafetyDetector {
    contains_unsafe: bool,
}

impl<'tcx> Visitor<'tcx> for UnsafetyDetector {
    fn nested_visit_map<'this>(&'this mut self) -> NestedVisitorMap<'this, 'tcx> {
        NestedVisitorMap::None
    }

    fn visit_block(&mut self, block: &hir::Block) {
        intravisit::walk_block(self, block);
        match block.rules {
            hir::BlockCheckMode::DefaultBlock => {}
            hir::BlockCheckMode::UnsafeBlock(_)
            | hir::BlockCheckMode::PushUnsafeBlock(_)
            | hir::BlockCheckMode::PopUnsafeBlock(_) => {
                self.contains_unsafe = true;
            }
        }
    }
}
