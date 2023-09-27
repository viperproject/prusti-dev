use jni::objects::JObject;
use systest::{get_jvm, print_exception, wrappers::*};

#[test]
#[cfg(debug_assertions)]
#[should_panic(
    expected = "Java binding type failure. Expected object of class java/lang/String, but got java/lang/Integer instead"
)]
fn constructor_should_fail_on_wrong_argument() {
    let jvm = get_jvm().expect("failed go get jvm reference");

    let env = jvm
        .attach_current_thread()
        .expect("failed to attach jvm thread");

    env.with_local_frame(16, || {
        let integer_object = java::lang::Integer::with(&env).new(1337)?;
        let error_wrapper = java::lang::Error::with(&env);
        let _result = error_wrapper.new(integer_object);
        Ok(JObject::null())
    })
    .unwrap_or_else(|e| {
        print_exception(&env);
        panic!("{} source: {:?}", e, std::error::Error::source(&e));
    });
}
