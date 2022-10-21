// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use proc_macro2::TokenStream;
use std::{
    io::Write,
    process::{Command, Stdio},
};

/// Try to pretty-print a tokenstream by piping it through `rustfmt`.
pub fn pretty_print_tokenstream(tokens: &TokenStream) -> Vec<u8> {
    let mut child = Command::new("rustfmt")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    {
        let stdin = child.stdin.as_mut().unwrap();
        stdin.write_all(tokens.to_string().as_bytes()).unwrap();
    }
    match child.wait_with_output() {
        Ok(output) => output.stdout,
        Err(error) => unreachable!("Pretty printing failed: {}", error),
    }
}
