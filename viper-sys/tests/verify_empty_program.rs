extern crate env_logger;
extern crate error_chain;
extern crate jni;
#[macro_use]
extern crate log;
extern crate viper_sys;

use error_chain::ChainedError;
use jni::objects::JObject;
use jni::InitArgsBuilder;
use jni::JNIVersion;
use jni::JavaVM;
use std::convert::From;
use std::env;
use std::fs;
use viper_sys::get_system_out;
use viper_sys::wrappers::*;

#[test]
fn verify_empty_program() {
    env_logger::init();

    let viper_home = env::var("VIPER_HOME").expect("failed to get VIPER_HOME");
    debug!("Using Viper home: '{}'", &viper_home);

    let z3_path = env::var("Z3_EXE").expect("failed to get Z3_EXE");
    debug!("Using Z3 path: '{}'", &z3_path);

    let jar_paths: Vec<String> = fs::read_dir(viper_home)
        .unwrap()
        .map(|x| x.unwrap().path().to_str().unwrap().to_string())
        .filter(|x| !x.contains("carbon"))
        .collect();

    let classpath_separator = if cfg!(windows) { ";" } else { ":" };
    let jvm_args = InitArgsBuilder::new()
        .version(JNIVersion::V8)
        .option(&format!("-Djava.class.path={}", jar_paths.join(classpath_separator)))
        .option("-Xdebug")
        //.option("-verbose:gc")
        //.option("-Xcheck:jni")
        //.option("-XX:+CheckJNICalls")
        //.option("-Djava.security.debug=all")
        //.option("-verbose:jni")
        //.option("-XX:+TraceJNICalls")
        .build()
        .unwrap_or_else(|e| {
            panic!("{}", e.display_chain());
        });

    let jvm = JavaVM::new(jvm_args).unwrap_or_else(|e| {
        panic!("{}", e.display_chain());
    });

    let env = jvm
        .attach_current_thread()
        .expect("failed to attach jvm thread");

    env.with_local_frame(32, || {
        let reporter = viper::silver::reporter::NoopReporter_object::with(&env).singleton()?;
        let plugin_aware_reporter = viper::silver::plugin::PluginAwareReporter::with(&env).new(reporter)?;
        let debug_info = scala::collection::immutable::Nil_object::with(&env).singleton()?;
        let silicon = viper::silicon::Silicon::with(&env).new(plugin_aware_reporter, debug_info)?;
        let verifier = viper::silver::verifier::Verifier::with(&env);

        let silicon_args_array =
            JObject::from(env.new_object_array(4, "java/lang/String", JObject::null())?);

        env.set_object_array_element(
            *silicon_args_array,
            0,
            env.new_string("--z3Exe")?,
        )?;

        env.set_object_array_element(
            *silicon_args_array,
            1,
            env.new_string(&z3_path)?,
        )?;

        env.set_object_array_element(
            *silicon_args_array,
            2,
            env.new_string("--ignoreFile")?,
        )?;

        env.set_object_array_element(
            *silicon_args_array,
            3,
            env.new_string("dummy.vpr")?,
        )?;

        let silicon_args_seq = scala::Predef::with(&env).call_wrapRefArray(silicon_args_array)?;

        verifier.call_parseCommandLine(silicon, silicon_args_seq)?;

        verifier.call_start(silicon)?;

        let program = viper::silver::ast::Program::with(&env).new(
            scala::collection::immutable::Nil_object::with(&env).singleton()?,
            scala::collection::immutable::Nil_object::with(&env).singleton()?,
            scala::collection::immutable::Nil_object::with(&env).singleton()?,
            scala::collection::immutable::Nil_object::with(&env).singleton()?,
            scala::collection::immutable::Nil_object::with(&env).singleton()?,
            scala::collection::immutable::Nil_object::with(&env).singleton()?,
            viper::silver::ast::NoPosition_object::with(&env).singleton()?,
            viper::silver::ast::NoInfo_object::with(&env).singleton()?,
            viper::silver::ast::NoTrafos_object::with(&env).singleton()?,
        )?;

        let verification_result = verifier.call_verify(silicon, program)?;

        let system_out = get_system_out(&env)?;

        java::io::PrintStream::with(&env).call_println(system_out, verification_result)?;

        verifier.call_stop(silicon)?;

        Ok(JObject::null())
    })
    .unwrap_or_else(|e| {
        let exception_occurred = env
            .exception_check()
            .unwrap_or_else(|e| panic!("{:?}", e));
        if exception_occurred {
            env.exception_describe()
                .unwrap_or_else(|e| panic!("{:?}", e));
        }
        panic!("{}", e.display_chain());
    });
}
