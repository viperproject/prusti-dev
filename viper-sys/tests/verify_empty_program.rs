use jni::{objects::JObject, InitArgsBuilder, JNIVersion, JavaVM};
use log::debug;
use std::{env, fs};
use viper_sys::{get_system_out, wrappers::*};

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
        .option(&format!(
            "-Djava.class.path={}",
            jar_paths.join(classpath_separator)
        ))
        .option("-Xdebug")
        //.option("-verbose:gc")
        //.option("-Xcheck:jni")
        //.option("-XX:+CheckJNICalls")
        //.option("-Djava.security.debug=all")
        //.option("-verbose:jni")
        //.option("-XX:+TraceJNICalls")
        .build()
        .unwrap_or_else(|e| {
            panic!("{} source: {:?}", e, std::error::Error::source(&e));
        });

    let jvm = JavaVM::new(jvm_args).unwrap_or_else(|e| {
        panic!("{} source: {:?}", e, std::error::Error::source(&e));
    });

    let env = jvm
        .attach_current_thread()
        .expect("failed to attach jvm thread");

    env.with_local_frame(32, || {
        let reporter = viper::silver::reporter::NoopReporter_object::with(&env).singleton()?;
        let debug_info = scala::collection::immutable::Nil_object::with(&env).singleton()?;
        let silicon = viper::silicon::Silicon::with(&env).new(reporter, debug_info)?;
        let verifier = viper::silver::verifier::Verifier::with(&env);

        let array_buffer_wrapper = scala::collection::mutable::ArrayBuffer::with(&env);
        let silicon_args_array = array_buffer_wrapper.new(4)?;

        array_buffer_wrapper.call_append(silicon_args_array, *env.new_string("--z3Exe")?)?;

        array_buffer_wrapper.call_append(silicon_args_array, *env.new_string(&z3_path)?)?;

        array_buffer_wrapper.call_append(silicon_args_array, *env.new_string("--ignoreFile")?)?;

        array_buffer_wrapper.call_append(silicon_args_array, *env.new_string("dummy.vpr")?)?;

        let silicon_args_seq = array_buffer_wrapper.call_toSeq(silicon_args_array)?;

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
        let exception_occurred = env.exception_check().unwrap_or_else(|e| panic!("{e:?}"));
        if exception_occurred {
            env.exception_describe().unwrap_or_else(|e| panic!("{e:?}"));
        }
        panic!("{} source: {:?}", e, std::error::Error::source(&e));
    });
}
