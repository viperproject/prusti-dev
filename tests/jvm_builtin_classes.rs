extern crate viper_sys;
extern crate jni;

use jni::JNIEnv;
use jni::objects::JObject;
use jni::objects::JValue::{Int, Object};
use viper_sys::{build_jvm, panic_on_jvm_exception};

#[test]
fn test_jvm_builtin_classes() {
    let jvm_options = [
        //"-Djava.security.debug=all",
        "-verbose:gc",
        //"-verbose:jni",
        "-Xcheck:jni",
        "-Xdebug",
        "-XX:+CheckJNICalls",
        //"-XX:+TraceJNICalls",
    ];

    let (_, raw_jvm_env) = unsafe { build_jvm(&jvm_options) };

    let env: JNIEnv = unsafe { JNIEnv::from_raw(raw_jvm_env).ok().unwrap() };

    for int_value in -10..10 {
        for array_length in 1..50 {
            // TODO: why this works even with 0 capacity?
            env.push_local_frame(0).ok().unwrap();

            let integer_value = env.new_object("java/lang/Integer", "(I)V", &[Int(int_value)])
                .ok()
                .map(|x| JObject::from(x))
                .and_then(|x| env.new_global_ref(x).ok())
                .unwrap();

            panic_on_jvm_exception(&env);

            let int_array =
                env.new_object_array(array_length, "java/lang/Integer", integer_value.as_obj())
                    .ok()
                    .map(|x| JObject::from(x))
                    .and_then(|x| env.new_global_ref(x).ok())
                    .unwrap();

            panic_on_jvm_exception(&env);

            let result = env.call_static_method(
                "java/util/Arrays",
                "binarySearch",
                "([Ljava/lang/Object;Ljava/lang/Object;)I",
                &[Object(int_array.as_obj()), Object(integer_value.as_obj())],
            ).ok()
                .and_then(|x| x.i().ok())
                .unwrap();

            panic_on_jvm_exception(&env);

            assert!(0 <= result && result < array_length);

            // TODO: it would be great to check the result of this call (see #jni-rs/issues/55)
            let _ = env.pop_local_frame(JObject::null());
        }
    }
}
