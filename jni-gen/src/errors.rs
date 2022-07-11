// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use jni;
use std;

// Create the Error, ErrorKind, ResultExt, and Result types
error_chain::error_chain! {
    foreign_links {
        Io(std::io::Error);
        Utf8Error(std::str::Utf8Error);
        // FIXME: why is this required?
        UnknownJniError(jni::errors::Error);
        UnknownJvmError(jni::JvmError);
    }


    errors {
        NoClass(class: String) {
            description("no class")
            display("no class '{}'", class)
        }

        NoConstructors(class: String) {
            description("no constructor")
            display("no constructors in class '{}'", class)
        }

        AmbiguousConstructor(class: String, signatures: Vec<String>) {
            description("ambiguous constructor")
            display("ambiguous constructor in class '{}'. Possible signatures: {}.", class, signatures.join(", "))
        }

        NoMatchingConstructor(class: String, signature: String) {
            description("no matching constructor")
            display("no constructor in class '{}' with signature '{}'", class, signature)
        }

        NoMethod(class: String, method: String) {
            description("no method")
            display("no method '{}' in class '{}'", method, class)
        }

        AmbiguousMethod(class: String, method: String, signatures: Vec<String>) {
            description("ambiguous method")
            display("ambiguous method '{}' in class '{}'. Possible signatures: {}.", method, class, signatures.join(", "))
        }

        NoMatchingMethod(class: String, method: String, signature: String) {
            description("no matching method")
            display("no method '{}' with signature '{}' in class '{}'", method, signature, class)
        }
    }
}
