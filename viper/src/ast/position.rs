// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::jar::{
    viper::silver::ast::{self, Position},
    java,
};
use crate::scala::new_option;
use duchess::{IntoJava, JavaConstructor, JavaField};
use duchess::java::lang::String as JavaString;

pub fn no_position() -> impl JavaField<Position> {
    ast::NoPosition__::get_module()
}

pub fn line_column_position(line: i32, column: i32) -> impl JavaConstructor<Position> {
    ast::LineColumnPosition::new(line, column)
}

pub fn identifier_position(
    line: i32,
    column: i32,
    pos_id: impl IntoJava<JavaString>,
) -> impl JavaConstructor<Position> {
    ast::IdentifierPosition::new(
        java::nio::file::Paths::get("", []),
        line_column_position(line, column),
        new_option(None),
        pos_id,
    )
}
