// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#[macro_export]
macro_rules! new_ast_node_with_pos {
    ($($java_class:ident)::+) => {
        $($java_class)::+::new(
            $crate::ast::no_info(),
            $crate::ast::no_trafos(),
        )
    };
    ($($java_class:ident)::+, $($args:expr),+) => {
        $($java_class)::+::new(
            $($args),+ ,
            $crate::ast::no_info(),
            $crate::ast::no_trafos(),
        )
    };
}

#[macro_export]
macro_rules! new_ast_node {
    ($($java_class:ident)::+) => {
         new_ast_node_with_pos!(
            $($java_class)::+,
            $crate::ast::no_position()
         )
    };
    ($($java_class:ident)::+, $($args:expr),+) => {
         new_ast_node_with_pos!(
            $($java_class)::+,
            $($args),+ ,
            $crate::ast::no_position()
         )
    };
}
