use jni::JNIEnv;
use jni::objects::{JObject, JValue};
use jni::errors::Error;

pub_scala_object_getter!(get_none, "scala/None");
pub_scala_object_getter!(get_predef, "scala/Predef");

pub fn java_array_to_seq<'a>(env: &'a JNIEnv, scala_predef: JObject, array: JObject) -> Result<JObject<'a>, Error> {
    env.call_method(
        scala_predef,
        "wrapRefArray",
        "([Ljava/lang/Object;)Lscala/collection/mutable/WrappedArray;",
        &[JValue::Object(array)],
    ).and_then(|x| x.l())
}
