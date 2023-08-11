// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Encoders of resources, their leak checks, and features that use resources (time reasoning).
//! Resource accesses are encoded in the pure code interpreter

mod interface;
mod time_reasoning;

pub(crate) use interface::ResourceEncoderInterface;
pub(crate) use time_reasoning::TimeReasoningInterface;
