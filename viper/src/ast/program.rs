// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::jar::{
    viper::silver::ast::{
        self, Domain, DomainFunc, Exp, Field, Function, LocalVarDecl, Method, NamedDomainAxiom,
        Position, Predicate, Stmt, Type,
    },
    scala::{self, collection::immutable::{Seq, Map}},
};
use super::{no_position, no_trafos, no_info, simple_info};
use crate::scala::new_option;
use duchess::{IntoJava, JavaConstructor};
use duchess::java::lang::String as JavaString;

pub fn program(
    domains: impl IntoJava<Seq<ast::Domain>>,
    fields: impl IntoJava<Seq<ast::Field>>,
    functions: impl IntoJava<Seq<ast::Function>>,
    predicates: impl IntoJava<Seq<ast::Predicate>>,
    methods: impl IntoJava<Seq<ast::Method>>,
) -> impl JavaConstructor<ast::Program> {
    new_ast_node!(ast::Program, domains, fields, functions, predicates, methods, &[])
}

pub fn field(
    name: impl IntoJava<JavaString>, typ: impl IntoJava<Type>,
) -> impl JavaConstructor<Field> {
    new_ast_node!(
        ast::Field,
        name,
        typ
    )
}

pub fn local_var_decl(
    name: impl IntoJava<JavaString>, typ: impl IntoJava<Type>,
) -> impl JavaConstructor<LocalVarDecl> {
    new_ast_node!(
        ast::LocalVarDecl,
        name,
        typ
    )
}

pub fn predicate(
    name: impl IntoJava<JavaString>,
    formal_args: impl IntoJava<Seq<LocalVarDecl>>,
    body: impl IntoJava<scala::Option<Exp>>,
) -> impl JavaConstructor<Predicate> {
    new_ast_node!(
        ast::Predicate,
        name,
        formal_args,
        body
    )
}

pub fn predicate_with_annotations(
    name: impl IntoJava<JavaString>,
    formal_args: impl IntoJava<Seq<LocalVarDecl>>,
    body: impl IntoJava<scala::Option<Exp>>,
    annotations: impl IntoJava<Map<JavaString, Seq<String>>>,
) -> impl JavaConstructor<Predicate> {
    ast::Predicate::new(
        name,
        formal_args,
        body,
        no_position(),
        ast::AnnotationInfo::new(annotations),
        no_trafos(),
    )
}

#[allow(clippy::too_many_arguments)]
pub fn function(
    name: impl IntoJava<JavaString>,
    formal_args: impl IntoJava<Seq<LocalVarDecl>>,
    typ: impl IntoJava<Type>,
    pres: impl IntoJava<Seq<Exp>>,
    posts: impl IntoJava<Seq<Exp>>,
    pos: Position,
    body: impl IntoJava<scala::Option<Exp>>,
) -> impl JavaConstructor<Function> {
    ast::Function::new(
        name,
        formal_args,
        typ,
        pres,
        posts,
        body,
        pos,
        no_info(),
        no_trafos(),
    )
}

pub fn method(
    name: impl IntoJava<JavaString>,
    formal_args: impl IntoJava<Seq<LocalVarDecl>>,
    formal_returns: impl IntoJava<Seq<LocalVarDecl>>,
    pres: impl IntoJava<Seq<Exp>>,
    posts: impl IntoJava<Seq<Exp>>,
    body: Option<Stmt>,
) -> impl JavaConstructor<Method> {
    ast::Method::new(
        name,
        formal_args,
        formal_returns,
        pres,
        posts,
        body,
        no_position(),
        no_info(),
        no_trafos(),
    )
}

pub fn domain(
    name: impl IntoJava<JavaString>,
    functions: impl IntoJava<Seq<DomainFunc>>,
    axioms: impl IntoJava<Seq<NamedDomainAxiom>>,
    type_vars: impl IntoJava<Seq<Type>>,
) -> impl JavaConstructor<Domain> {
    new_ast_node!(
        ast::Domain,
        name,
        functions,
        axioms,
        type_vars,
        new_option(None)
    )
}

pub fn domain_func(
    name: impl IntoJava<JavaString>,
    formal_args: impl IntoJava<Seq<LocalVarDecl>>,
    typ: impl IntoJava<Type>,
    unique: bool,
    domain_name: impl IntoJava<JavaString>,
) -> impl JavaConstructor<DomainFunc> {
    ast::DomainFunc::new(
        name,
        formal_args,
        typ,
        unique,
        new_option(None),
        no_position(),
        no_info(),
        domain_name,
        no_trafos(),
    )
}

pub fn named_domain_axiom(
    name: impl IntoJava<JavaString>,
    expr: Exp,
    domain_name: impl IntoJava<JavaString>,
) -> impl JavaConstructor<NamedDomainAxiom> {
    ast::NamedDomainAxiom::new(
        name,
        expr,
        no_position(),
        no_info(),
        domain_name,
        no_trafos(),
    )
}

pub fn named_domain_axiom_with_comment(
    name: impl IntoJava<JavaString>,
    expr: Exp,
    domain_name: impl IntoJava<JavaString>,
    comment: impl IntoJava<JavaString>,
) -> impl JavaConstructor<NamedDomainAxiom> {
    ast::NamedDomainAxiom::new(
        name,
        expr,
        no_position(),
        simple_info(&[comment]),
        domain_name,
        no_trafos(),
    )
}

pub fn backend_type(
    name: impl IntoJava<JavaString>,
    functions: impl IntoJava<Seq<DomainFunc>>,
    interpretations: impl IntoJava<Map<String, String>>,
) -> impl JavaConstructor<Domain> {
    new_ast_node!(
        ast::Domain,
        name,
        functions,
        &[],
        &[],
        new_option(Some(interpretations))
    )
}

pub fn backend_func(
    name: impl IntoJava<JavaString>,
    formal_args: impl IntoJava<Seq<LocalVarDecl>>,
    typ: impl IntoJava<Type>,
    domain_name: impl IntoJava<JavaString>,
    interpretation: impl IntoJava<JavaString>,
) -> impl JavaConstructor<DomainFunc> {
    ast::DomainFunc::new(
        name,
        formal_args,
        typ,
        false,
        new_option(Some(interpretation)),
        no_position(),
        no_info(),
        domain_name,
        no_trafos(),
    )
}
