extern crate viper_sys;
extern crate jni;

use jni::JNIEnv;
use jni::objects::{JObject, JValue};
use viper_sys::{build_jvm, panic_on_jvm_exception};
use viper_sys::verifier::*;
use std::fs;

#[test]
fn test_jvm_builtin_classes() {
    let jar_paths: Vec<String> = fs::read_dir("/usr/lib/viper/").unwrap().map(
        |x| x.unwrap().path().to_str().unwrap().to_owned()
    ).collect();

    let jvm_options = [
        &format!("-Djava.class.path={}", jar_paths.join(":")),
        //"-Djava.security.debug=all",
        "-verbose:gc",
        //"-verbose:jni",
        "-Xcheck:jni",
        "-Xdebug",
        "-XX:+CheckJNICalls",
        //"-XX:+TraceJNICalls",
    ];

    println!("JVM options: {}", jvm_options.join(" "));

    let (_, raw_jvm_env) = unsafe { build_jvm(&jvm_options) };

    let env: JNIEnv = unsafe { JNIEnv::from_raw(raw_jvm_env).ok().unwrap() };

    let silicon = new_silicon(&env).ok().unwrap();

    panic_on_jvm_exception(&env);

    let args = env.new_object_array(0, "java/lang/String", JObject::null()).ok()
        .map(|x| JObject::from(x))
        .map(|x| JValue::Object(x))
        .unwrap();

    parse_command_line(&env, silicon, args);

    panic_on_jvm_exception(&env);

    start(&env, silicon);

    panic_on_jvm_exception(&env);

    restart(&env, silicon);

    panic_on_jvm_exception(&env);

    stop(&env, silicon);

    panic_on_jvm_exception(&env);
}
