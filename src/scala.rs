use jni::JNIEnv;
use jni::sys::jint;
use jni::objects::{JObject, JValue};
use jni::errors::Error;

pub_scala_object_getter!(get_none, "scala/None");
pub_scala_object_getter!(get_predef, "scala/Predef");

pub fn new_some<'a>(env: &'a JNIEnv, object: JObject) -> Result<JObject<'a>, Error> {
    env.new_object(
        "scala/Some",
        "([Ljava/lang/Object;)V",
        &[JValue::Object(object)],
    )
}

pub fn wrap_ref_array<'a>(
    env: &'a JNIEnv,
    scala_predef: JObject,
    array: JObject,
) -> Result<JObject<'a>, Error> {
    env.call_method(
        scala_predef,
        "wrapRefArray",
        "([Ljava/lang/Object;)Lscala/collection/mutable/WrappedArray;",
        &[JValue::Object(array)],
    ).and_then(|x| x.l())
}

pub fn new_mutable_array_seq<'a>(env: &'a JNIEnv, size: jint) -> Result<JObject<'a>, Error> {
    env.new_object(
        "scala/collection/mutable/ArraySeq",
        "(I)V",
        &[JValue::Int(size)],
    )
}

pub fn update_mutable_array_seq<'a>(
    env: &'a JNIEnv,
    mutable_array_seq: JObject,
    index: jint,
    element: JObject,
) -> Result<(), Error> {
    env.call_method(
        mutable_array_seq,
        "update",
        "(ILjava/lang/Object;)V",
        &[JValue::Int(index), JValue::Object(element)],
    ).map(|_| ())
}
