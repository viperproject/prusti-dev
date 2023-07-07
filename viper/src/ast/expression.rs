// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::jar::{
    viper::silver::ast::{
        self, DomainFunc, Exp, Field, LocalVarDecl, Location, Position, Trigger, Type,
    },
    scala::collection::immutable::{Map, Seq},
    java::math::BigInteger,
};
use duchess::{IntoJava, JavaConstructor};
use duchess::java::lang::String as JavaString;

pub fn add_with_pos(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(
        ast::Add,
        left,
        right,
        pos
    )
}

pub fn add(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    add_with_pos(left, right, super::no_position())
}

pub fn sub_with_pos(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(
        ast::Sub,
        left,
        right,
        pos
    )
}

pub fn sub(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    sub_with_pos(left, right, super::no_position())
}

pub fn mul_with_pos(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(
        ast::Mul,
        left,
        right,
        pos
    )
}

pub fn mul(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    mul_with_pos(left, right, super::no_position())
}

pub fn div_with_pos(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(
        ast::Div,
        left,
        right,
        pos
    )
}

pub fn div(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    div_with_pos(left, right, super::no_position())
}

pub fn module_with_pos(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(
        ast::Mod,
        left,
        right,
        pos
    )
}

pub fn module(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    module_with_pos(left, right, super::no_position())
}

pub fn lt_cmp_with_pos(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(
        ast::LtCmp,
        left,
        right,
        pos
    )
}

pub fn lt_cmp(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    lt_cmp_with_pos(left, right, super::no_position())
}

pub fn le_cmp_with_pos(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(
        ast::LeCmp,
        left,
        right,
        pos
    )
}

pub fn le_cmp(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    le_cmp_with_pos(left, right, super::no_position())
}

pub fn gt_cmp_with_pos(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(
        ast::GtCmp,
        left,
        right,
        pos
    )
}

pub fn gt_cmp(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    gt_cmp_with_pos(left, right, super::no_position())
}

pub fn ge_cmp_with_pos(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(
        ast::GeCmp,
        left,
        right,
        pos
    )
}

pub fn ge_cmp(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    ge_cmp_with_pos(left, right, super::no_position())
}

pub fn eq_cmp_with_pos(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(
        ast::EqCmp,
        left,
        right,
        pos
    )
}

pub fn eq_cmp(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    eq_cmp_with_pos(left, right, super::no_position())
}

pub fn ne_cmp_with_pos(left: impl IntoJava<Exp>, right: impl IntoJava<Exp>, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(
        ast::NeCmp,
        left,
        right,
        pos
    )
}

pub fn ne_cmp(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    ne_cmp_with_pos(left, right, super::no_position())
}

pub fn int_lit_with_pos(
    i: i64, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    let big_i = BigInteger::new(i.to_string());
    new_ast_node_with_pos!(ast::IntLit, big_i, pos)
}

pub fn int_lit(i: i64) -> impl JavaConstructor<Exp> {
 int_lit_with_pos(i, super::no_position())
}

pub fn int_lit_from_string_with_pos(
    i: impl IntoJava<JavaString>, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    let big_i = BigInteger::new(i);
    new_ast_node_with_pos!(ast::IntLit, big_i, pos)
}

pub fn int_lit_from_string(i: impl IntoJava<JavaString>) -> impl JavaConstructor<Exp> {
    int_lit_from_string_with_pos(i, super::no_position())
}

pub fn minus_with_pos(
    expr: impl IntoJava<Exp>, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(ast::Minus, expr, pos)
}

pub fn minus(
    expr: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    minus_with_pos(expr, super::no_position())
}

pub fn or_with_pos(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(
        ast::Or,
        left,
        right,
        pos
    )
}

pub fn or(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    or_with_pos(left, right, super::no_position())
}

pub fn and_with_pos(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(
        ast::And,
        left,
        right,
        pos
    )
}

pub fn and(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    and_with_pos(left, right, super::no_position())
}

pub fn implies_with_pos(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(
        ast::Implies,
        left,
        right,
        pos
    )
}

pub fn implies(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::Implies,
        left,
        right
    )
}

pub fn magic_wand_with_pos(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(
        ast::MagicWand,
        left,
        right,
        pos
    )
}

pub fn magic_wand(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    magic_wand_with_pos(left, right, super::no_position())
}

pub fn not_with_pos(
    expr: impl IntoJava<Exp>, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(ast::Not, expr, pos)
}

pub fn not(
    expr: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    not_with_pos(expr, super::no_position())
}

pub fn true_lit_with_pos(
    pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(ast::TrueLit, pos)
}

pub fn true_lit() -> impl JavaConstructor<Exp> {
    true_lit_with_pos(super::no_position())
}

pub fn false_lit_with_pos(
    pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(ast::FalseLit, pos)
}

pub fn false_lit() -> impl JavaConstructor<Exp> {
    false_lit_with_pos(super::no_position())
}

pub fn null_lit_with_pos(
    pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(ast::NullLit, pos)
}

pub fn null_lit() -> impl JavaConstructor<Exp> {
    null_lit_with_pos(super::no_position())
}

pub fn field_access_predicate_with_pos(
    loc: impl IntoJava<Exp>,
    perm: impl IntoJava<Exp>,
    pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(
        ast::FieldAccessPredicate,
        loc,
        perm,
        pos
    )
}

pub fn field_access_predicate(
    loc: impl IntoJava<Exp>, perm: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    field_access_predicate_with_pos(loc, perm, super::no_position())
}

pub fn predicate_access_predicate_with_pos(
    loc: impl IntoJava<Exp>,
    perm: impl IntoJava<Exp>,
    pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(
        ast::PredicateAccessPredicate,
        loc,
        perm,
        pos
    )
}

pub fn predicate_access_predicate(
    loc: impl IntoJava<Exp>, perm: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    predicate_access_predicate_with_pos(loc, perm, super::no_position())
}

pub fn inhale_exhale_pred(
    inhale: impl IntoJava<Exp>, exhale: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::InhaleExhaleExp,
        inhale,
        exhale
    )
}

pub fn wildcard_perm() -> impl JavaConstructor<Exp> {
    new_ast_node!(ast::WildcardPerm)
}

pub fn full_perm() -> impl JavaConstructor<Exp> {
    new_ast_node!(ast::FullPerm)
}

pub fn no_perm() -> impl JavaConstructor<Exp> {
    new_ast_node!(ast::NoPerm)
}

pub fn epsilon_perm() -> impl JavaConstructor<Exp> {
    new_ast_node!(ast::EpsilonPerm)
}

pub fn fractional_perm(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::FractionalPerm,
        left,
        right
    )
}

pub fn perm_div(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::PermDiv,
        left,
        right
    )
}

pub fn current_perm(
    loc: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(ast::CurrentPerm, loc)
}

pub fn perm_minus(
    expr: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(ast::PermMinus, expr)
}

pub fn perm_add(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::PermAdd,
        left,
        right
    )
}

pub fn perm_sub(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::PermSub,
        left,
        right
    )
}

pub fn perm_mul(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::PermMul,
        left,
        right
    )
}

pub fn int_perm_mul(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::IntPermMul,
        left,
        right
    )
}

pub fn perm_lt_cmp(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::PermLtCmp,
        left,
        right
    )
}

pub fn perm_le_cmp(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::PermLeCmp,
        left,
        right
    )
}

pub fn perm_gt_cmp(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::PermGtCmp,
        left,
        right
    )
}

pub fn perm_ge_cmp(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::PermGeCmp,
        left,
        right
    )
}

pub fn func_app(
    function_name: impl IntoJava<JavaString>,
    args: impl IntoJava<Seq<Exp>>,
    return_type: Type,
    pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    ast::FuncApp::apply(function_name, args).apply(
        pos,
        super::no_info(),
        return_type,
        super::no_trafos(),
    )
}

pub fn domain_func_app2(
    function_name: impl IntoJava<JavaString>,
    args: impl IntoJava<Seq<Exp>>,
    type_var_map: impl IntoJava<Map<Type, Type>>,
    return_type: Type,
    domain_name: impl IntoJava<JavaString>,
    pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    ast::DomainFuncApp::apply(function_name, args, type_var_map).apply(
        pos,
        super::no_info(),
        return_type,
        domain_name,
        super::no_trafos(),
    )
}

pub fn domain_func_app(
    domain_func: DomainFunc,
    args: impl IntoJava<Seq<Exp>>,
    type_var_map: impl IntoJava<Map<Type, Type>>,
) -> impl JavaConstructor<Exp> {
    ast::DomainFuncApp__::get_module()
        .apply(domain_func, args, type_var_map)
        .apply(super::no_info(), super::no_trafos())
}

pub fn field_access_with_pos(
    rcv: impl IntoJava<Exp>, field: Field, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(
        ast::FieldAccess,
        rcv,
        field,
        pos
    )
}

pub fn field_access(rcv: impl IntoJava<Exp>, field: Field) -> impl JavaConstructor<Exp> {
    field_access_with_pos(rcv, field, super::no_position())
}

pub fn predicate_access(
    args: impl IntoJava<Seq<Exp>>, predicate_name: impl IntoJava<JavaString>
) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::PredicateAccess,
        args,
        predicate_name
    )
}

pub fn predicate_access_with_pos(
    args: impl IntoJava<Seq<Exp>>,
    predicate_name: impl IntoJava<JavaString>,
    pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(
        ast::PredicateAccess,
        args,
        predicate_name,
        pos
    )
}

pub fn cond_exp_with_pos(
    cond: impl IntoJava<Exp>,
    then_expr: impl IntoJava<Exp>,
    else_expr: impl IntoJava<Exp>,
    pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(
        ast::CondExp,
        cond,
        then_expr,
        else_expr,
        pos
    )
}

pub fn cond_exp(
    cond: impl IntoJava<Exp>, then_expr: impl IntoJava<Exp>, else_expr: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    cond_exp_with_pos(cond, then_expr, else_expr, super::no_position())
}

pub fn unfolding_with_pos(
    acc: impl IntoJava<Exp>, body: impl IntoJava<Exp>, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(
        ast::Unfolding,
        acc,
        body,
        pos
    )
}

pub fn unfolding(
    acc: impl IntoJava<Exp>, body: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    unfolding_with_pos(acc, body, super::no_position())
}

pub fn applying(
    wand: impl IntoJava<Exp>, body: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::Applying,
        wand,
        body
    )
}

pub fn old(
    expr: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(ast::Old, expr)
}

pub fn labelled_old_with_pos(
    expr: impl IntoJava<Exp>, old_label: impl IntoJava<JavaString>, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(
        ast::LabelledOld,
        expr,
        old_label,
        pos
    )
}

pub fn labelled_old(expr: impl IntoJava<Exp>, old_label: impl IntoJava<JavaString>) -> impl JavaConstructor<Exp> {
    labelled_old_with_pos(expr, old_label, super::no_position())
}

pub fn let_expr_with_pos(
    variable: LocalVarDecl,
    expr: impl IntoJava<Exp>,
    body: impl IntoJava<Exp>,
    pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(
        ast::Let,
        variable,
        expr,
        body,
        pos
    )
}

pub fn let_expr(
    variable: LocalVarDecl, expr: impl IntoJava<Exp>, body: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    let_expr_with_pos(variable, expr, body, super::no_position())
}

pub fn forall_with_pos(
    variables: impl IntoJava<Seq<LocalVarDecl>>,
    triggers: impl IntoJava<Seq<Trigger>>,
    expr: impl IntoJava<Exp>,
    pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(
        ast::Forall,
        variables,
        triggers,
        expr,
        pos
    )
}

pub fn forall(
    variables: impl IntoJava<Seq<LocalVarDecl>>, triggers: impl IntoJava<Seq<Trigger>>, expr: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    forall_with_pos(variables, triggers, expr, super::no_position())
}

pub fn exists_with_pos(
    variables: impl IntoJava<Seq<LocalVarDecl>>,
    triggers: impl IntoJava<Seq<Trigger>>,
    expr: impl IntoJava<Exp>,
    pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(
        ast::Exists,
        variables,
        triggers,
        expr,
        pos
    )
}

pub fn exists(
    variables: impl IntoJava<Seq<LocalVarDecl>>, triggers: impl IntoJava<Seq<Trigger>>, expr: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    exists_with_pos(variables, triggers, expr, super::no_position())
}

pub fn for_perm(
    variable: LocalVarDecl,
    access_list: impl IntoJava<Seq<Location>>,
    body: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::ForPerm,
        variable,
        access_list,
        body
    )
}

pub fn trigger_with_pos(
    exps: impl IntoJava<Seq<Exp>>, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Trigger> {
    new_ast_node_with_pos!(
        ast::Trigger,
        exps,
        pos
    )
}

pub fn trigger(exps: impl IntoJava<Seq<Exp>>) -> impl JavaConstructor<Trigger> {
    trigger_with_pos(exps, super::no_position())
}

pub fn local_var_with_pos(
    name: impl IntoJava<JavaString>, var_type: Type, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(
        ast::LocalVar,
        name,
        var_type,
        pos
    )
}

pub fn local_var(name: impl IntoJava<JavaString>, var_type: Type) -> impl JavaConstructor<Exp> {
    local_var_with_pos(name, var_type, super::no_position())
}

pub fn result_with_pos(
    var_type: Type, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Exp> {
    new_ast_node_with_pos!(
        ast::Result,
        var_type,
        pos
    )
}

pub fn empty_seq(elem_type: Type) -> impl JavaConstructor<Exp> {
    new_ast_node!(ast::EmptySeq, elem_type)
}

pub fn explicit_seq(elems: impl IntoJava<Seq<Exp>>) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::ExplicitSeq,
        elems
    )
}

pub fn empty_map(key_ty: Type, val_ty: Type) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::EmptyMap,
        key_ty,
        val_ty
    )
}

pub fn explicit_map(keys_values: impl IntoJava<Seq<Exp>>) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::ExplicitMap,
        keys_values
    )
}

pub fn update_map(
    map: impl IntoJava<Exp>, key: impl IntoJava<Exp>, val: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::MapUpdate,
        map,
        key,
        val
    )
}

pub fn lookup_map(
    map: impl IntoJava<Exp>, key: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::MapLookup,
        map,
        key
    )
}

pub fn map_contains(
    map: impl IntoJava<Exp>, key: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::MapContains,
        key,
        map
    )
}

pub fn map_len(
    map: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(ast::MapCardinality, map)
}

pub fn range_seq(
    low: impl IntoJava<Exp>, high: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::RangeSeq,
        low,
        high
    )
}

pub fn seq_append(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::SeqAppend,
        left,
        right
    )
}

pub fn seq_index(
    seq: impl IntoJava<Exp>, index: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::SeqIndex,
        seq,
        index
    )
}

pub fn seq_take(
    seq: impl IntoJava<Exp>, num: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(ast::SeqTake, seq, num)
}

pub fn seq_drop(
    seq: impl IntoJava<Exp>, num: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(ast::SeqDrop, seq, num)
}

pub fn seq_contains(
    elem: impl IntoJava<Exp>, seq: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::SeqContains,
        elem,
        seq
    )
}

pub fn seq_update(
    seq: impl IntoJava<Exp>, index: impl IntoJava<Exp>, elem: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::SeqUpdate,
        seq,
        index,
        elem
    )
}

pub fn seq_length(
    seq: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(ast::SeqLength, seq)
}

pub fn empty_set(elem_type: Type) -> impl JavaConstructor<Exp> {
    new_ast_node!(ast::EmptySet, elem_type)
}

pub fn explicit_set(elems: impl IntoJava<Seq<Exp>>) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::ExplicitSet,
        elems
    )
}

pub fn empty_multiset(elem_type: Type) -> impl JavaConstructor<Exp> {
    new_ast_node!(ast::EmptyMultiset, elem_type)
}

pub fn explicit_multiset(elems: impl IntoJava<Seq<Exp>>) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::ExplicitMultiset,
        elems
    )
}

pub fn any_set_union(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::AnySetUnion,
        left,
        right
    )
}

pub fn any_set_intersection(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::AnySetIntersection,
        left,
        right
    )
}

pub fn any_set_subset(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::AnySetSubset,
        left,
        right
    )
}

pub fn any_set_minus(
    left: impl IntoJava<Exp>, right: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::AnySetMinus,
        left,
        right
    )
}

pub fn any_set_contains(
    elem: impl IntoJava<Exp>, set: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(
        ast::AnySetContains,
        elem,
        set
    )
}

pub fn any_set_cardinality(
    set: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    new_ast_node!(ast::AnySetCardinality, set)
}

pub fn simplified_expression(
    expr: impl IntoJava<Exp>,
) -> impl JavaConstructor<Exp> {
    ast::utility::Simplifier__::get_module().simplify(expr)
}
