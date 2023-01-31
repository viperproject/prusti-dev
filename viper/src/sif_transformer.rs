// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{ast_factory::Program, ast_utils::AstUtils, jni_utils::JniUtils};
use jni::JNIEnv;
use log::debug;
use viper_sys::wrappers::viper::silver;

pub struct SIFTransformer<'a> {
    env: &'a JNIEnv<'a>,
    jni: JniUtils<'a>,
    ast_utils: AstUtils<'a>,
}

impl<'a> SIFTransformer<'a> {
    pub fn new(env: &'a JNIEnv) -> Self {
        let jni = JniUtils::new(env);
        let ast_utils = AstUtils::new(env);
        SIFTransformer {
            env,
            jni,
            ast_utils,
        }
    }

    #[must_use]
    pub fn sif_transformation(self, program: Program<'a>) -> Program<'a> {
        debug!(
            "Program before transformation:\n{}",
            self.ast_utils.pretty_print(program)
        );

        let sif_transformer = silver::sif::SIFExtendedTransformer_object::with(self.env);

        run_timed!("SIF transformation", debug,
            let transformed_program = self.jni.unwrap_result(
                sif_transformer
                    .call_transform(self.jni.unwrap_result(sif_transformer.singleton()), program.to_jobject(), false),
            );
        );

        debug_assert!(self
            .env
            .is_instance_of(
                transformed_program,
                self.env.find_class("viper/silver/ast/Program").unwrap(),
            )
            .unwrap());

        let transformed_program = Program::new(transformed_program);
        debug!(
            "Program after transformation:\n{}",
            self.ast_utils.pretty_print(transformed_program)
        );
        transformed_program
    }
}
