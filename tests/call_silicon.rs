extern crate viper_sys;
extern crate jni;
extern crate env_logger;
extern crate error_chain;

use std::fs;
use std::convert::From;
use jni::JNIEnv;
use jni::objects::JObject;
use error_chain::ChainedError;
use viper_sys::java::*;
use viper_sys::scala::*;
use viper_sys::jvm::*;
use viper_sys::verifier::*;
use viper_sys::viper_ast::*;

#[test]
fn test_call_silicon() {
    env_logger::init().unwrap();

    let jar_paths: Vec<String> = fs::read_dir("/usr/lib/viper/")
        .unwrap()
        .map(|x| x.unwrap().path().to_str().unwrap().to_owned())
        .collect();

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

    let silicon = new_silicon(&env).unwrap_or_else(|e| {
        print_exception(&env);
        println!("{}", e.display_chain().to_string());
        panic!();
    });

    let silicon_args_array = env.new_object_array(3, "java/lang/String", JObject::null())
        .ok()
        .map(|x| JObject::from(x))
        .unwrap();

    let mut arg;

    arg = env.new_string("--z3Exe").unwrap_or_else(|e| {
        print_exception(&env);
        println!("{}", e.display_chain().to_string());
        panic!();
    });
    env.set_object_array_element(silicon_args_array.into_inner(), 0, From::from(arg))
        .unwrap_or_else(|e| {
            print_exception(&env);
            println!("{}", e.display_chain().to_string());
            panic!();
        });

    arg = env.new_string("/usr/local/Viper/z3/bin/z3")
        .unwrap_or_else(|e| {
            print_exception(&env);
            println!("{}", e.display_chain().to_string());
            panic!();
        });
    env.set_object_array_element(silicon_args_array.into_inner(), 1, From::from(arg))
        .unwrap_or_else(|e| {
            print_exception(&env);
            println!("{}", e.display_chain().to_string());
            panic!();
        });

    arg = env.new_string("dummy-program.sil").unwrap_or_else(|e| {
        print_exception(&env);
        println!("{}", e.display_chain().to_string());
        panic!();
    });
    env.set_object_array_element(silicon_args_array.into_inner(), 2, From::from(arg))
        .unwrap_or_else(|e| {
            print_exception(&env);
            println!("{}", e.display_chain().to_string());
            panic!();
        });

    let scala_predef = get_predef(&env).unwrap_or_else(|e| {
        print_exception(&env);
        println!("{}", e.display_chain().to_string());
        panic!();
    });

    let silicon_args_seq = wrap_ref_array(&env, scala_predef, silicon_args_array)
        .unwrap_or_else(|e| {
            print_exception(&env);
            println!("{}", e.display_chain().to_string());
            panic!();
        });

    parse_command_line(&env, silicon, silicon_args_seq).unwrap_or_else(|e| {
        print_exception(&env);
        println!("{}", e.display_chain().to_string());
        panic!();
    });

    start(&env, silicon).unwrap_or_else(|e| {
        print_exception(&env);
        println!("{}", e.display_chain().to_string());
        panic!();
    });

    reset(&env, silicon).unwrap_or_else(|e| {
        print_exception(&env);
        println!("{}", e.display_chain().to_string());
        panic!();
    });

    let domains = new_mutable_array_seq(&env, 0).unwrap_or_else(|e| {
        print_exception(&env);
        println!("{}", e.display_chain().to_string());
        panic!();
    });

    let fields = new_mutable_array_seq(&env, 0).unwrap_or_else(|e| {
        print_exception(&env);
        println!("{}", e.display_chain().to_string());
        panic!();
    });

    let functions = new_mutable_array_seq(&env, 0).unwrap_or_else(|e| {
        print_exception(&env);
        println!("{}", e.display_chain().to_string());
        panic!();
    });

    let predicates = new_mutable_array_seq(&env, 0).unwrap_or_else(|e| {
        print_exception(&env);
        println!("{}", e.display_chain().to_string());
        panic!();
    });

    let methods = new_mutable_array_seq(&env, 0).unwrap_or_else(|e| {
        print_exception(&env);
        println!("{}", e.display_chain().to_string());
        panic!();
    });

    let position = get_no_position(&env).unwrap_or_else(|e| {
        print_exception(&env);
        println!("{}", e.display_chain().to_string());
        panic!();
    });

    let info = get_no_info(&env).unwrap_or_else(|e| {
        print_exception(&env);
        println!("{}", e.display_chain().to_string());
        panic!();
    });

    let errt = get_no_trafos(&env).unwrap_or_else(|e| {
        print_exception(&env);
        println!("{}", e.display_chain().to_string());
        panic!();
    });

    let program_object = get_program_object(&env).unwrap_or_else(|e| {
        print_exception(&env);
        println!("{}", e.display_chain().to_string());
        panic!();
    });

    let program = new_program(
        &env,
        program_object,
        domains,
        fields,
        functions,
        predicates,
        methods,
        position,
        info,
        errt,
    ).unwrap_or_else(|e| {
        print_exception(&env);
        println!("{}", e.display_chain().to_string());
        panic!();
    });

    let verification_result = verify(&env, silicon, program).unwrap_or_else(|e| {
        print_exception(&env);
        println!("{}", e.display_chain().to_string());
        panic!();
    });

    let system_out = get_system_out(&env).unwrap_or_else(|e| {
        print_exception(&env);
        println!("{}", e.display_chain().to_string());
        panic!();
    });

    println_object(&env, system_out, verification_result).unwrap_or_else(|e| {
        print_exception(&env);
        println!("{}", e.display_chain().to_string());
        panic!();
    });

    stop(&env, silicon).unwrap_or_else(|e| {
        print_exception(&env);
        println!("{}", e.display_chain().to_string());
        panic!();
    });
}
