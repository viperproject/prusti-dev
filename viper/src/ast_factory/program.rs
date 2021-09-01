// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use ast_factory::{
    structs::{
        Domain, DomainFunc, Expr, Field, Function, LocalVarDecl, Method, NamedDomainAxiom,
        Position, Predicate, Program, Stmt, Type,
    },
    AstFactory,
};
use jni::objects::JObject;
use viper_sys::wrappers::viper::silver::ast;

impl<'a> AstFactory<'a> {
    pub fn program(
        &self,
        domains: &[Domain],
        fields: &[Field],
        functions: &[Function],
        predicates: &[Predicate],
        methods: &[Method],
    ) -> Program<'a> {
        build_ast_node!(
            self,
            Program,
            ast::Program,
            self.jni.new_seq(&map_to_jobjects!(domains)),
            self.jni.new_seq(&map_to_jobjects!(fields)),
            self.jni.new_seq(&map_to_jobjects!(functions)),
            self.jni.new_seq(&map_to_jobjects!(predicates)),
            self.jni.new_seq(&map_to_jobjects!(methods)),
            self.jni.new_seq(&[])
        )
    }

    pub fn field(&self, name: &str, typ: Type) -> Field<'a> {
        build_ast_node!(
            self,
            Field,
            ast::Field,
            self.jni.new_string(name),
            typ.to_jobject()
        )
    }

    pub fn local_var_decl(&self, name: &str, typ: Type) -> LocalVarDecl<'a> {
        build_ast_node!(
            self,
            LocalVarDecl,
            ast::LocalVarDecl,
            self.jni.new_string(name),
            typ.to_jobject()
        )
    }

    pub fn predicate(
        &self,
        name: &str,
        formal_args: &[LocalVarDecl],
        body: Option<Expr>,
    ) -> Predicate<'a> {
        build_ast_node!(
            self,
            Predicate,
            ast::Predicate,
            self.jni.new_string(name),
            self.jni.new_seq(&map_to_jobjects!(formal_args)),
            match body {
                None => self.jni.new_option(None),
                Some(x) => self.jni.new_option(Some(x.to_jobject())),
            }
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub fn function(
        &self,
        name: &str,
        formal_args: &[LocalVarDecl],
        typ: Type,
        pres: &[Expr],
        posts: &[Expr],
        pos: Position,
        body: Option<Expr>,
    ) -> Function<'a> {
        let obj = self.jni.unwrap_result(ast::Function::with(self.env).new(
            self.jni.new_string(name),
            self.jni.new_seq(&map_to_jobjects!(formal_args)),
            typ.to_jobject(),
            self.jni.new_seq(&map_to_jobjects!(pres)),
            self.jni.new_seq(&map_to_jobjects!(posts)),
            match body {
                None => self.jni.new_option(None),
                Some(x) => self.jni.new_option(Some(x.to_jobject())),
            },
            pos.to_jobject(),
            self.no_info(),
            self.no_trafos(),
        ));
        Function::new(obj)
    }

    pub fn method(
        &self,
        name: &str,
        formal_args: &[LocalVarDecl],
        formal_returns: &[LocalVarDecl],
        pres: &[Expr],
        posts: &[Expr],
        body: Option<Stmt>,
    ) -> Method<'a> {
        let obj = self.jni.unwrap_result(ast::Method::with(self.env).new(
            self.jni.new_string(name),
            self.jni.new_seq(&map_to_jobjects!(formal_args)),
            self.jni.new_seq(&map_to_jobjects!(formal_returns)),
            self.jni.new_seq(&map_to_jobjects!(pres)),
            self.jni.new_seq(&map_to_jobjects!(posts)),
            match body {
                None => self.jni.new_option(None),
                Some(x) => self.jni.new_option(Some(x.to_jobject())),
            },
            self.no_position().to_jobject(),
            self.no_info(),
            self.no_trafos(),
        ));
        Method::new(obj)
    }

    pub fn domain(
        &self,
        name: &str,
        functions: &[DomainFunc],
        axioms: &[NamedDomainAxiom],
        type_vars: &[Type],
    ) -> Domain<'a> {
        build_ast_node!(
            self,
            Domain,
            ast::Domain,
            self.jni.new_string(name),
            self.jni.new_seq(&map_to_jobjects!(functions)),
            self.jni.new_seq(&map_to_jobjects!(axioms)),
            self.jni.new_seq(&map_to_jobjects!(type_vars))
        )
    }

    pub fn domain_func(
        &self,
        name: &str,
        formal_args: &[LocalVarDecl],
        typ: Type,
        unique: bool,
        domain_name: &str,
    ) -> DomainFunc<'a> {
        let obj = self.jni.unwrap_result(ast::DomainFunc::with(self.env).new(
            self.jni.new_string(name),
            self.jni.new_seq(&map_to_jobjects!(formal_args)),
            typ.to_jobject(),
            unique,
            self.no_position().to_jobject(),
            self.no_info(),
            self.jni.new_string(domain_name),
            self.no_trafos(),
        ));
        DomainFunc::new(obj)
    }

    pub fn named_domain_axiom(
        &self,
        name: &str,
        expr: Expr,
        domain_name: &str,
    ) -> NamedDomainAxiom<'a> {
        let obj = self
            .jni
            .unwrap_result(ast::NamedDomainAxiom::with(self.env).new(
                self.jni.new_string(name),
                expr.to_jobject(),
                self.no_position().to_jobject(),
                self.no_info(),
                self.jni.new_string(domain_name),
                self.no_trafos(),
            ));
        NamedDomainAxiom::new(obj)
    }
}
