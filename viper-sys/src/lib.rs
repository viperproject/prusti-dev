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
