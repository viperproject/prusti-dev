// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::rc::Rc;

use prusti_rustc_interface::{
    index::vec::IndexVec,
    middle::mir::{BasicBlock, Body},
};

use crate::{translation, MicroStatement, MicroTerminator};

#[derive(Clone, Debug)]
pub struct MicroBody<'tcx> {
    pub basic_blocks: MicroBasicBlocks<'tcx>,
    pub body: Rc<Body<'tcx>>,
}
impl<'tcx> MicroBody<'tcx> {
    pub fn new(body: Rc<Body<'tcx>>) -> Self {
        let basic_blocks = translation::translate_bbs(&body);
        Self { basic_blocks, body }
    }
}

#[derive(Clone, Debug)]
pub struct MicroBasicBlocks<'tcx> {
    pub basic_blocks: IndexVec<BasicBlock, MicroBasicBlockData<'tcx>>,
}

#[derive(Clone, Debug)]
pub struct MicroBasicBlockData<'tcx> {
    pub statements: Vec<MicroStatement<'tcx>>,
    pub terminator: Option<MicroTerminator<'tcx>>,
    pub is_cleanup: bool,
}
