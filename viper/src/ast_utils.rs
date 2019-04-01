// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use jni::JNIEnv;
use jni::objects::JObject;
use ast_factory::Program;
use viper_sys::wrappers::viper::*;
use jni_utils::JniUtils;

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

    pub(crate) fn check_consistency(&self, program: Program) -> Vec<JObject> {
        self.jni.seq_to_vec(self.jni.unwrap_result(
            silver::ast::Node::with(self.env).call_checkTransitively(program.to_jobject()),
        ))
    }

    pub fn pretty_print(&self, program: Program) -> String {
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

    pub fn to_string(&self, program: Program) -> String {
        self.jni.to_string(program.to_jobject())
    }

    pub fn ensure_local_capacity(&self, capacity: i32) {
        self.env.ensure_local_capacity(capacity);
    }
}
