#![feature(impl_trait_in_assoc_type)]

mod to_viper;

use duchess::java::lang::{Object, String};
use duchess::prelude::*;

use duchess::Jvm;

use viper_defs::scala::collection::immutable::Seq;
use viper_defs::scala::collection::mutable::ArrayBuffer;
use viper_defs::scala::Tuple2;

fn empty_scala_seq<T: duchess::JavaObject>() -> impl IntoJava<Seq<T>> {
    ArrayBuffer::new(0).to_seq().assert_not_null()
}

pub fn verify<'vir>(program: vir::Program<'vir>) {
    /*
    fn seq_of_vec<T: duchess::JavaObject + duchess::TryJDeref>(vec: Vec<T>) -> impl IntoJava<Seq<T>> {
        let buffer = ArrayBuffer::new(vec.len() as i32);
        for obj in vec.iter() {
            buffer.append(obj);
        }
        buffer.to_seq().assert_not_null()
    }
    */

    // convert program
    use crate::to_viper::ToViper;
    let jprogram = program.to_viper();

    duchess::Jvm::with(|jvm| {
        // create arguments for command-line
        let args = vec![
            "--z3Exe=/r/prusti-dev-rewrite/viper_tools/z3/bin/z3",
            // "--boogieExe=..",
            "--ignoreFile", "dummy.vpr",
        ];
        let jargs_buf = ArrayBuffer::<String>::new(args.len() as i32).execute_with(jvm)?;
        for obj in args.iter() {
            let arg_str = obj.to_string().to_java::<String>().execute_with(jvm)?;
            jargs_buf.append(&arg_str).execute_with(jvm)?;
        }
        let jargs = viper_defs::scala::collection::IterableOnceOps::to_seq(&jargs_buf).execute_with(jvm)?;

        // create reporter, debug info
        let reporter = viper_defs::viper::silver::reporter::NoopReporter__::get_module().execute_with(jvm)?;
        let debug_info = empty_scala_seq::<Tuple2<String, Object>>();

        // create backend
        let backend = viper_defs::viper::silicon::Silicon::new(&reporter, debug_info).execute_with(jvm)?;

        // create logger
        let logger_factory = viper_defs::viper::silver::logger::SilentLogger::apply().execute_with(jvm)?;
        let logger = viper_defs::viper::silver::logger::ViperLogger::get(&logger_factory).execute_with(jvm)?;

        // create frontend
        let frontend = viper_defs::viper::silicon::SiliconFrontend::new(&reporter, &logger).execute_with(jvm)?;

        // override backend with ours
        let backend_option = viper_defs::scala::Some::new(&backend).execute_with(jvm)?;
        viper_defs::viper::silver::frontend::DefaultFrontend::verifier_eq(&frontend, &backend_option).execute_with(jvm)?;
        viper_defs::viper::silver::frontend::SilFrontend::set_verifier(&frontend, &backend).execute_with(jvm)?;

        // set frontend state
        let state = viper_defs::viper::silver::frontend::DefaultStates::consistency_check().execute_with(jvm)?;
        viper_defs::viper::silver::frontend::DefaultFrontend::set_state(&frontend, &state).execute_with(jvm)?;

        // pass command-line arguments
        viper_defs::viper::silver::verifier::Verifier::parse_command_line(&backend, &jargs).execute_with(jvm)?;

        // start backend
        viper_defs::viper::silver::verifier::Verifier::start(&backend).execute_with(jvm)?;

        // TODO: run consistency checks?

        // set program
        let program_option = viper_defs::scala::Some::new(&jprogram).execute_with(jvm)?;
        viper_defs::viper::silver::frontend::DefaultFrontend::program_eq(&frontend, &program_option).execute_with(jvm)?;

        // run verification
        viper_defs::viper::silver::frontend::DefaultFrontend::verification(&frontend).execute_with(jvm)?;

        // get results
        let result = viper_defs::viper::silver::frontend::DefaultFrontend::get_verification_result(&frontend).execute_with(jvm)?;

        println!("ok! silicon: {frontend:?}, result {result:?}");
        let res_str = result
            .unwrap()
            .to_string()
            .to_rust()
            .execute_with(jvm)?
            .unwrap();
        println!("result str: {res_str}");

        Ok(())
    }).unwrap();
}
