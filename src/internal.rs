// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! This module provides function stubs used for type-checking
//! specifications.

/// This function is used to provide expression id to the surrounding
/// function.
pub fn __id(_uuid: usize) {}

/// This function is used to type-check boolean assertions. The first
/// argument is the unique id of the expression. The second argument is
/// the expression itself.
pub fn __assertion(_uuid: usize, _spec: bool) {}

/// This function is used to type-check terms used in triggers. The
/// first argument is the unique id of the expression. The second
/// argument is the expression itself.
pub fn __trigger<T>(_uuid: usize, _spec: T) {}
