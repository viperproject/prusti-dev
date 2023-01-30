// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::jni_utils::JniUtils;
use crate::ast_utils::AstUtils;
use crate::ast_factory::Program;
use jni::JNIEnv;
use log::debug;
use viper_sys::wrappers::viper::silver;

pub struct SIFTransformer<'a> {
	env: &'a JNIEnv<'a>,
    jni: JniUtils<'a>,
    ast_utils: AstUtils<'a>,
}

impl<'a> SIFTransformer<'a> {
	pub fn new(
		env: &'a JNIEnv,
	) -> Self {
		let jni = JniUtils::new(env);
		let ast_utils = AstUtils::new(env);
		SIFTransformer { env, jni, ast_utils }
	}

    #[must_use]
    pub fn sif_transformation(self, program: Program<'a>) -> Program<'a> {
         self.ast_utils.with_local_frame(16, || {
            debug!("Program before transformation:\n{}", self.ast_utils.pretty_print(program));

            let sif_transformer = silver::sif::SIFExtendedTransformer_object::with(self.env);
            
            run_timed!("SIF transformation", debug, 
                let tranformed_program = Program::new(self.jni.unwrap_result(
                    sif_transformer
                        .call_transform(self.jni.unwrap_result(sif_transformer.singleton()), program.to_jobject(), false),
                ));
            );
            debug!("Program after transformation:\n{}", self.ast_utils.pretty_print(tranformed_program));
            tranformed_program
        })   
    }
}
