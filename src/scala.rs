use jni::JNIEnv;
use jni::objects::{JObject, JValue};
use jni::errors::Error;

pub fn get_predef<'a>(env: &'a JNIEnv) -> Result<JObject<'a>, Error> {
    env.get_static_field(
        "scala/Predef$",
        "MODULE$",
        "Lscala/Predef$;",
    ).and_then(|x| x.l())
}

pub fn java_array_to_seq<'a>(env: &'a JNIEnv, scala_predef: JObject, array: JObject) -> Result<JObject<'a>, Error> {
    env.call_method(
        scala_predef,
        "wrapRefArray",
        "([Ljava/lang/Object;)Lscala/collection/mutable/WrappedArray;",
        &[JValue::Object(array)],
    ).and_then(|x| x.l())
}
