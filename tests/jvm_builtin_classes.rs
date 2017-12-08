extern crate viper_sys;
extern crate jni;
extern crate error_chain;

use error_chain::ChainedError;
use jni::JNIEnv;
use jni::objects::JObject;
use jni::objects::JValue;
use viper_sys::jvm::*;

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
            env.with_local_frame(16, || {
                let integer_value = JObject::from(env.new_object(
                    "java/lang/Integer",
                    "(I)V",
                    &[JValue::Int(int_value)],
                )?);

                let int_array = JObject::from(env.new_object_array(
                    array_length,
                    "java/lang/Integer",
                    integer_value.as_obj(),
                )?);

                let result = env.call_static_method(
                    "java/util/Arrays",
                    "binarySearch",
                    "([Ljava/lang/Object;Ljava/lang/Object;)I",
                    &[
                        JValue::Object(int_array.as_obj()),
                        JValue::Object(integer_value.as_obj()),
                    ],
                )?
                    .i()?;

                assert!(0 <= result && result < array_length);

            }).unwrap_or_else(|e| {
                    print_exception(&env);
                    panic!(format!("{}", e.display_chain().to_string()));
                });
        }
    }
}
