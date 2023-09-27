use jni::{errors::Result as JNIResult, objects::JObject, JNIEnv};
use systest::{get_jvm, print_exception, wrappers::*};

fn string_to_jobject<'a>(env: &JNIEnv<'a>, string: &str) -> JNIResult<JObject<'a>> {
    Ok(JObject::from(env.new_string(string.to_owned())?))
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(
    expected = "Java binding type failure. Expected object of class java/lang/Error, but got java/lang/Integer instead"
)]
fn field_setter_should_fail_on_wrong_receiver() {
    let jvm = get_jvm().expect("failed go get jvm reference");

    let env = jvm
        .attach_current_thread()
        .expect("failed to attach jvm thread");

    env.with_local_frame(16, || {
        let error_wrapper = java::lang::Error::with(&env);
        let integer_object = java::lang::Integer::with(&env).new(1337)?;
        error_wrapper
            .set_detailMessage(integer_object, string_to_jobject(&env, "error message")?)?;
        Ok(JObject::null())
    })
    .unwrap_or_else(|e| {
        print_exception(&env);
        panic!("{} source: {:?}", e, std::error::Error::source(&e));
    });
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(
    expected = "Java binding type failure. Expected object of class java/lang/String, but got java/lang/Integer instead"
)]
fn field_setter_should_fail_on_wrong_argument() {
    let jvm = get_jvm().expect("failed go get jvm reference");

    let env = jvm
        .attach_current_thread()
        .expect("failed to attach jvm thread");

    env.with_local_frame(16, || {
        let error_wrapper = java::lang::Error::with(&env);
        let error_object = error_wrapper.new(string_to_jobject(&env, "error message")?)?;
        let integer_object = java::lang::Integer::with(&env).new(1337)?;
        error_wrapper.set_detailMessage(error_object, integer_object)?;
        Ok(JObject::null())
    })
    .unwrap_or_else(|e| {
        print_exception(&env);
        panic!("{} source: {:?}", e, std::error::Error::source(&e));
    });
}
