// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![deny(unused_must_use)]
#![warn(clippy::disallowed_types)]

#[rustfmt::skip]
#[path = "../gen/mod.rs"]
pub mod wrappers;

use jni::{errors::Result, objects::JObject, JNIEnv};
use jni_gen::utils::java_str_to_string;

pub fn get_system_out<'a>(env: &'a JNIEnv) -> Result<JObject<'a>> {
    env.get_static_field("java/lang/System", "out", "Ljava/io/PrintStream;")
        .and_then(|x| x.l())
}

fn get_jobject_class_name_inner<'a, 'c, O>(env: &'c JNIEnv<'c>, object: O) -> Result<String>
where
    O: Into<JObject<'a>>
{
    let object_class = env.get_object_class(object)?;
    let res = java_str_to_string(
        &env.get_string(
            env.call_method(object_class, "getName", "()Ljava/lang/String;", &[])?
                 .l()?
                 .into(),
        )?,
    );

    match res {
        Ok(str) => Ok(str),
        Err(_) => Ok("Cannot be determined".to_string()),
    }
}

pub fn get_jobject_class_name<'a, O>(env: &'a JNIEnv<'a>, object: O) -> String
where
    O: Into<JObject<'a>>
{
    match get_jobject_class_name_inner(env, object) {
        Ok(result) => result,
        Err(_) => "Cannot be determined".to_string(),
    }
}
