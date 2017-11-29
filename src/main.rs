extern crate jni_sys;
extern crate jni;

use jni::JNIEnv;
use jni::objects::JObject;
use jni::objects::JValue::{Int, Object};
use lib::{build_jvm, panic_on_jvm_exception};

mod lib;

fn main() {
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

    let array_length = 10;

    let integer_value_42 = env.new_object("java/lang/Integer", "(I)V", &[Int(42)])
        .ok()
        .map(|x| JObject::from(x))
        .and_then(|x| env.new_global_ref(x).ok())
        .unwrap();

    panic_on_jvm_exception(&env);

    let int_array =
        env.new_object_array(array_length, "java/lang/Integer", integer_value_42.as_obj())
            .ok()
            .map(|x| JObject::from(x))
            .and_then(|x| env.new_global_ref(x).ok())
            .unwrap();

    panic_on_jvm_exception(&env);

    let result = env.call_static_method(
        "java/util/Arrays",
        "binarySearch",
        "([Ljava/lang/Object;Ljava/lang/Object;)I",
        &[
            Object(int_array.as_obj()),
            Object(integer_value_42.as_obj()),
        ],
    ).ok()
        .and_then(|x| x.i().ok())
        .unwrap();

    panic_on_jvm_exception(&env);

    println!("Result: {:?}", result);

    assert!(0 <= result && result < array_length);

    println!("Done");
}
