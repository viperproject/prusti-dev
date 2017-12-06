use jni::JNIEnv;
use jni::objects::{JObject, JValue};
use jni::errors::Error;

pub fn to_string<'a>(env: &'a JNIEnv, object: JObject) -> Result<JObject<'a>, Error> {
    env.call_method(object, "toString", "()Ljava/lang/String;", &[])
        .and_then(|x| x.l())
}

pub fn get_system_out<'a>(env: &'a JNIEnv) -> Result<JObject<'a>, Error> {
    env.get_static_field("java/lang/System", "out", "Ljava/io/PrintStream;")
        .and_then(|x| x.l())
}

pub fn println_object<'a>(
    env: &'a JNIEnv,
    system_out: JObject,
    object: JObject,
) -> Result<(), Error> {
    env.call_method(
        system_out,
        "println",
        "(Ljava/lang/Object;)V",
        &[JValue::Object(object)],
    ).map(|_| ())
}
