// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

pub trait HoareSemantics {
    type PRE;
    type POST;
    fn precondition(&self) -> Self::PRE;
    fn postcondition(&self) -> Self::POST;
}
