// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

extern crate jni;

#[path = "../gen/mod.rs"]
pub mod wrappers;

use jni::JNIEnv;
use jni::objects::JObject;
use jni::errors::Result;

pub fn get_system_out<'a>(env: &'a JNIEnv) -> Result<JObject<'a>> {
    env.get_static_field("java/lang/System", "out", "Ljava/io/PrintStream;")
        .and_then(|x| x.l())
}
