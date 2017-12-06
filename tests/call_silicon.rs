extern crate viper_sys;
extern crate jni;
extern crate env_logger;

use std::fs;
use std::convert::From;
use jni::JNIEnv;
use jni::objects::JObject;
use viper_sys::jvm::*;
use viper_sys::verifier::*;
use viper_sys::scala::*;

#[test]
fn test_call_silicon() {
    env_logger::init().unwrap();

    let jar_paths: Vec<String> = fs::read_dir("/usr/lib/viper/").unwrap().map(
        |x| x.unwrap().path().to_str().unwrap().to_owned()
    ).collect();

    let jvm_options = [
        &format!("-Djava.class.path={}", jar_paths.join(":")),
        //"-Djava.security.debug=all",
        //"-verbose:gc",
        //"-verbose:jni",
        //"-Xcheck:jni",
        "-Xdebug",
        //"-XX:+CheckJNICalls",
        //"-XX:+TraceJNICalls",
    ];

    println!("JVM options: {}", jvm_options.join(" "));

    let (_, raw_jvm_env) = unsafe { build_jvm(&jvm_options) };

    let env: JNIEnv = unsafe { JNIEnv::from_raw(raw_jvm_env).ok().unwrap() };

    let silicon = new_silicon(&env)
        .unwrap_or_else(|e| { print_exception(&env); panic!(e); });

    let silicon_args_array = env.new_object_array(3, "java/lang/String", JObject::null()).ok()
        .map(|x| JObject::from(x))
        .unwrap();

    let mut arg;

    arg = env.new_string("--z3Exe")
        .unwrap_or_else(|e| { print_exception(&env); panic!(e); });
    env.set_object_array_element(silicon_args_array.into_inner(), 0, From::from(arg))
        .unwrap_or_else(|e| { print_exception(&env); panic!(e); });

    arg = env.new_string("/usr/local/Viper/z3/bin/z3")
        .unwrap_or_else(|e| { print_exception(&env); panic!(e); });
    env.set_object_array_element(silicon_args_array.into_inner(), 1, From::from(arg))
        .unwrap_or_else(|e| { print_exception(&env); panic!(e); });

    arg = env.new_string("dummy-program.sil")
        .unwrap_or_else(|e| { print_exception(&env); panic!(e); });
    env.set_object_array_element(silicon_args_array.into_inner(), 2, From::from(arg))
        .unwrap_or_else(|e| { print_exception(&env); panic!(e); });

    let scala_predef = get_predef(&env)
        .unwrap_or_else(|e| { print_exception(&env); panic!(e); });

    let silicon_args_seq = java_array_to_seq(&env, scala_predef, silicon_args_array)
        .unwrap_or_else(|e| { print_exception(&env); panic!(e); });

    parse_command_line(&env, silicon, silicon_args_seq)
        .unwrap_or_else(|e| { print_exception(&env); panic!(e); });

    start(&env, silicon)
        .unwrap_or_else(|e| { print_exception(&env); panic!(e); });

    reset(&env, silicon)
        .unwrap_or_else(|e| { print_exception(&env); panic!(e); });

    stop(&env, silicon)
        .unwrap_or_else(|e| { print_exception(&env); panic!(e); });
}
