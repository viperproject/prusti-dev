// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::jar::{
    viper::silver::ast::{
        NoInfo__,
        SimpleInfo,
        NoTrafos__,
    },
    scala::collection::immutable::Seq,
};
use duchess::{IntoJava, JavaConstructor, JavaField};
use duchess::java::lang::String as JavaString;

pub fn no_info() -> impl JavaField<NoInfo__> {
    NoInfo__::get_module()
}

pub fn simple_info(
    comments: impl IntoJava<Seq<JavaString>>
) -> impl JavaConstructor<SimpleInfo> {
    SimpleInfo::new(comments)
}

pub fn no_trafos() -> impl JavaField<NoTrafos__> {
    NoTrafos__::get_module()
}
