// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{ast_factory::Program, jni_utils::JniUtils, JavaException};
use jni::{objects::JObject, JNIEnv};
use viper_sys::wrappers::viper::*;

#[derive(Clone, Copy)]
pub struct AstUtils<'a> {
    env: &'a JNIEnv<'a>,
    jni: JniUtils<'a>,
}

impl<'a> AstUtils<'a> {
    pub fn new(env: &'a JNIEnv) -> Self {
        let jni = JniUtils::new(env);
        AstUtils { env, jni }
    }

    /// Returns a vector of consistency errors, or a Java exception
    pub(crate) fn check_consistency(
        &self,
        program: Program<'a>,
    ) -> Result<Vec<JObject<'a>>, JavaException> {
        self.jni
            .unwrap_or_exception(
                silver::ast::Node::with(self.env).call_checkTransitively(program.to_jobject()),
            )
            .map(|java_vec| self.jni.seq_to_vec(java_vec))
    }

    pub fn pretty_print(&self, program: Program<'a>) -> String {
        let fast_pretty_printer_wrapper =
            silver::ast::pretty::FastPrettyPrinter_object::with(self.env);
        self.jni.get_string(
            self.jni.unwrap_result(
                fast_pretty_printer_wrapper.call_pretty(
                    self.jni
                        .unwrap_result(fast_pretty_printer_wrapper.singleton()),
                    program.to_jobject(),
                ),
            ),
        )
    }

    pub fn to_string(&self, program: Program<'a>) -> String {
        self.jni.to_string(program.to_jobject())
    }

    /// Important: the result of the `f` call must not contain Java objects. Use carefully.
    pub fn with_local_frame<T>(&self, capacity: i32, f: impl FnOnce() -> T) -> T {
        self.jni.unwrap_result(self.env.push_local_frame(capacity));
        let result = f();
        self.jni
            .unwrap_result(self.env.pop_local_frame(JObject::null()));
        result
    }
}
