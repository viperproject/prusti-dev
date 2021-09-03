// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

/// The structure describing a Java exception
#[derive(Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct JavaException {
    message: String,
    stack_trace: String,
}

impl JavaException {
    pub fn new(message: String, stack_trace: String) -> Self {
        JavaException {
            message,
            stack_trace,
        }
    }

    pub fn get_message(&self) -> &str {
        &self.message
    }

    pub fn get_stack_trace(&self) -> &str {
        &self.stack_trace
    }
}

impl std::fmt::Display for JavaException {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Java exception: {}", self.message)
    }
}

impl std::fmt::Debug for JavaException {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Java exception: {} - {}", self.message, self.stack_trace)
    }
}
