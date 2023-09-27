use jni::{errors::Result as JNIResult, objects::JObject, JNIEnv};
use systest::{get_jvm, print_exception, wrappers::*};

fn string_to_jobject<'a>(env: &JNIEnv<'a>, string: &str) -> JNIResult<JObject<'a>> {
    Ok(JObject::from(env.new_string(string.to_owned())?))
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(
    expected = "Java binding type failure. Expected object of class java/util/Random, but got java/lang/Error instead"
)]
fn static_method_should_fail_on_wrong_receiver() {
    let jvm = get_jvm().expect("failed go get jvm reference");

    let env = jvm
        .attach_current_thread()
        .expect("failed to attach jvm thread");

    env.with_local_frame(16, || {
        let big_integer_wrapper = java::math::BigInteger::with(&env);
        let error_wrapper = java::lang::Error::with(&env);
        let error_object = error_wrapper.new(string_to_jobject(&env, "error message")?)?;
        let _result = big_integer_wrapper.call_probablePrime(1337, error_object);
        Ok(JObject::null())
    })
    .unwrap_or_else(|e| {
        print_exception(&env);
        panic!("{} source: {:?}", e, std::error::Error::source(&e));
    });
}
