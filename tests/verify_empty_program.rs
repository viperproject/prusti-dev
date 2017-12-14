extern crate viper_sys;
extern crate jni;
extern crate error_chain;

use std::fs;
use std::convert::From;
use jni::JavaVM;
use jni::InitArgsBuilder;
use jni::JNIVersion;
use jni::objects::JObject;
use error_chain::ChainedError;
use viper_sys::print_exception;
use viper_sys::get_system_out;
use viper_sys::wrappers::*;

#[test]
fn verify_empty_program() {
    let jar_paths: Vec<String> = fs::read_dir("/usr/lib/viper/")
        .unwrap()
        .map(|x| x.unwrap().path().to_str().unwrap().to_owned())
        .collect();

    let jvm_args = InitArgsBuilder::new()
        .version(JNIVersion::V8)
        .option(&format!("-Djava.class.path={}", jar_paths.join(":")))
        .option("-verbose:gc")
        .option("-Xdebug")
        //.option("-Xcheck:jni")
        //.option("-XX:+CheckJNICalls")
        //.option("-Djava.security.debug=all")
        //.option("-verbose:jni")
        //.option("-XX:+TraceJNICalls")
        .build()
        .unwrap_or_else(|e| {
            panic!(format!("{}", e.display_chain().to_string()));
        });

    let jvm = JavaVM::new(jvm_args).unwrap_or_else(|e| {
        panic!(format!("{}", e.display_chain().to_string()));
    });


    let env = jvm.attach_current_thread().expect(
        "failed to attach jvm thread",
    );

    env.with_local_frame(32, || {
        let silicon = viper::silicon::Silicon::new(&env).construct()?;

        let silicon_args_array = JObject::from(
            env.new_object_array(3, "java/lang/String", JObject::null())?,
        );

        env.set_object_array_element(
            silicon_args_array.into_inner(),
            0,
            From::from(env.new_string("--z3Exe")?),
        )?;

        env.set_object_array_element(
            silicon_args_array.into_inner(),
            1,
            From::from(env.new_string("/usr/bin/viper-z3")?),
        )?;

        env.set_object_array_element(
            silicon_args_array.into_inner(),
            2,
            From::from(env.new_string("dummy-program.sil")?),
        )?;

        let silicon_args_seq = scala::Predef::new(&env).call_wrapRefArray(
            silicon_args_array,
        )?;

        viper::silicon::Silicon::new(&env).call_parseCommandLine(
            silicon,
            silicon_args_seq,
        )?;

        viper::silicon::Silicon::new(&env).call_start(silicon)?;

        let program = viper::silver::ast::Program::new(&env).construct(
            scala::collection::mutable::ArraySeq::new(&env).construct(0)?,
            scala::collection::mutable::ArraySeq::new(&env).construct(0)?,
            scala::collection::mutable::ArraySeq::new(&env).construct(0)?,
            scala::collection::mutable::ArraySeq::new(&env).construct(0)?,
            scala::collection::mutable::ArraySeq::new(&env).construct(0)?,
            viper::silver::ast::NoPosition_object::new(&env).get()?,
            viper::silver::ast::NoInfo_object::new(&env).get()?,
            viper::silver::ast::NoTrafos_object::new(&env).get()?,
        )?;

        let verification_result = viper::silicon::Silicon::new(&env).call_verify(
            silicon,
            program,
        )?;

        let system_out = get_system_out(&env)?;

        java::io::PrintStream::new(&env).call_println_6(
            system_out,
            verification_result,
        )?;

        viper::silicon::Silicon::new(&env).call_stop(silicon)?;

        Ok(JObject::null())

    }).unwrap_or_else(|e| {
            print_exception(&env);
            panic!(format!("{}", e.display_chain().to_string()));
        });
}
