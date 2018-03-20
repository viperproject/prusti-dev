// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

mod method;

use jni::JNIEnv;
use ast_factory::AstFactory;
use ast_factory::LocalVarDecl;

pub use self::method::*;

#[derive(Clone, Copy)]
pub struct CfgFactory<'a> {
    ast: AstFactory<'a>,
}

impl<'a> CfgFactory<'a> {
    pub fn new(env: &'a JNIEnv) -> Self {
        let ast = AstFactory::new(env);
        CfgFactory { ast }
    }

    pub fn new_cfg_method<IntoString>(
        &self,
        method_name: IntoString,
        formal_args: Vec<LocalVarDecl<'a>>,
        formal_returns: Vec<LocalVarDecl<'a>>,
        local_vars: Vec<LocalVarDecl<'a>>,
    ) -> CfgMethod
    where
        IntoString: Into<String>,
    {
        CfgMethod::new(
            &self.ast,
            method_name.into(),
            formal_args,
            formal_returns,
            local_vars,
        )
    }
}
