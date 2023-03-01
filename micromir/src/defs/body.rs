// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use derive_more::{Deref, DerefMut};
use prusti_rustc_interface::{
    index::vec::IndexVec,
    middle::{
        mir::{BasicBlock, BasicBlockData, Body},
        ty::TyCtxt,
    },
};
use std::rc::Rc;

use crate::{MicroStatement, MicroTerminator, PlaceCapabilitySummary};

#[derive(Clone, Debug, Deref, DerefMut)]
pub struct MicroBody<'tcx> {
    pub(crate) done_repacking: bool,
    pub basic_blocks: MicroBasicBlocks<'tcx>,
    #[deref]
    #[deref_mut]
    pub body: Rc<Body<'tcx>>,
}
impl<'tcx> MicroBody<'tcx> {
    pub fn new(body: Rc<Body<'tcx>>, tcx: TyCtxt<'tcx>) -> Self {
        let mut body = Self::from(body);
        body.calculate_repacking(tcx);
        body
    }
}

impl<'tcx> From<Rc<Body<'tcx>>> for MicroBody<'tcx> {
    /// Clones a `mir::Body` into an identical `MicroBody`.
    /// Doesn't calculate any repacking information.
    fn from(body: Rc<Body<'tcx>>) -> Self {
        let basic_blocks = MicroBasicBlocks::from(&*body);
        Self {
            done_repacking: false,
            basic_blocks,
            body,
        }
    }
}

#[derive(Clone, Debug)]
pub struct MicroBasicBlocks<'tcx> {
    pub basic_blocks: IndexVec<BasicBlock, MicroBasicBlockData<'tcx>>,
}

impl<'tcx> From<&Body<'tcx>> for MicroBasicBlocks<'tcx> {
    #[tracing::instrument(level = "debug", skip(body), fields(body = format!("{body:#?}")))]
    fn from(body: &Body<'tcx>) -> Self {
        Self {
            basic_blocks: body
                .basic_blocks
                .iter()
                .map(MicroBasicBlockData::from)
                .collect(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct MicroBasicBlockData<'tcx> {
    pub statements: Vec<MicroStatement<'tcx>>,
    pub terminator: MicroTerminator<'tcx>,
    pub is_cleanup: bool,
}

impl<'tcx> From<&BasicBlockData<'tcx>> for MicroBasicBlockData<'tcx> {
    fn from(data: &BasicBlockData<'tcx>) -> Self {
        Self {
            statements: data.statements.iter().map(MicroStatement::from).collect(),
            terminator: data.terminator().into(),
            is_cleanup: data.is_cleanup,
        }
    }
}

impl<'tcx> MicroBasicBlockData<'tcx> {
    pub(crate) fn get_pcs_mut(&mut self) -> Option<&mut PlaceCapabilitySummary<'tcx>> {
        self.terminator.repack_join.as_mut()
    }
}
