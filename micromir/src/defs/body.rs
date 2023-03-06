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
use std::{
    fmt::{Display, Formatter, Result},
    rc::Rc,
};

use crate::{
    FreeState, MicroStatement, MicroTerminator, TermDebug, TerminatorPlaceCapabilitySummary,
};

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
    #[tracing::instrument(level = "info", skip(body), fields(body = format!("{body:#?}")))]
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

impl Display for MicroBasicBlocks<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        for (bb, data) in self.basic_blocks.iter_enumerated() {
            writeln!(f, "{bb:?}: {{")?;
            for stmt in &data.statements {
                let repack = stmt.repack_operands.as_ref().unwrap();
                writeln!(f, "  // {}", repack.state())?;
                for rpck in &**repack.repacks() {
                    writeln!(f, "  {rpck:?};")?;
                }
                for (tmp, operand) in stmt.operands.iter_enumerated() {
                    writeln!(f, "  {tmp:?} <- {operand:?};")?;
                }
                writeln!(f, "  {:?};", stmt.kind)?;
            }
            let repack = data.terminator.repack_operands.as_ref().unwrap();
            writeln!(f, "  // {}", repack.state())?;
            for rpck in &**repack.repacks() {
                writeln!(f, "  {rpck:?};")?;
            }
            for (tmp, operand) in data.terminator.operands.iter_enumerated() {
                writeln!(f, "  {tmp:?} <- {operand:?};")?;
            }
            let display = TermDebug(&data.terminator.kind, &data.terminator.original_kind);
            writeln!(f, "  {display:?};")?;
            let repack = data.terminator.repack_join.as_ref().unwrap();
            // writeln!(f, "  // {}", repack.state())?;
            for (bb, repacks) in repack.repacks().iter() {
                if repacks.is_empty() {
                    continue;
                }
                writeln!(f, "  {bb:?}:")?;
                for rpck in &**repacks {
                    writeln!(f, "    {rpck:?};")?;
                }
            }
            writeln!(f, "}}")?;
        }
        Ok(())
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
    pub(crate) fn get_start_state(&self) -> &FreeState<'tcx> {
        if self.statements.is_empty() {
            self.terminator.repack_operands.as_ref().unwrap().state()
        } else {
            self.statements[0].repack_operands.as_ref().unwrap().state()
        }
    }
    pub(crate) fn get_end_pcs_mut(
        &mut self,
    ) -> Option<&mut TerminatorPlaceCapabilitySummary<'tcx>> {
        self.terminator.repack_join.as_mut()
    }
}
