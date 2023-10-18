// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt::{Display, Formatter, Result};

use prusti_rustc_interface::{
    middle::{mir::Local, ty::RegionVid}
};

use crate::{free_pcs::CapabilityKind, utils::Place};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CouplingOp {
    Add(Block),
    Remove(RegionVid, Vec<Block>),
    Activate(RegionVid),
}

impl CouplingOp {
    pub fn regions(&self) -> Box<dyn Iterator<Item = RegionVid> + '_> {
        match self {
            CouplingOp::Add(block) => Box::new([block.sup, block.sub].into_iter()),
            CouplingOp::Remove(remove, block) =>
                Box::new([*remove].into_iter().chain(block.iter().flat_map(|b| [b.sup, b.sub].into_iter()))),
            CouplingOp::Activate(region) => Box::new([*region].into_iter()),
        }
    }
}

impl Display for CouplingOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            CouplingOp::Add(block) => block.fmt(f),
            CouplingOp::Remove(remove, patch) => {
                write!(f, "Remove({remove:?}, {{")?;
                for p in patch {
                    write!(f, "\n  {p}")?;
                }
                if !patch.is_empty() {
                    write!(f, "\n")?;
                }
                write!(f, "}})")
            }
            CouplingOp::Activate(region) => write!(f, "Activate({region:?})"),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Block {
    /// The region that outlives (is blocked)
    pub sup: RegionVid,
    /// The region that must be outlived (is blocking)
    pub sub: RegionVid,
    // pub kind: CapabilityKind,
    pub waiting_to_activate: bool,
}
impl Display for Block {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let Block { sup, sub, waiting_to_activate } = *self;
        write!(f, "Block({sup:?}, {sub:?}){}", if waiting_to_activate { "?" } else { "" })
    }
}
