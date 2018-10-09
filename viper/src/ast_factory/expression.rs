// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use viper_sys::wrappers::viper::silver::ast;
use ast_factory::AstFactory;
use ast_factory::structs::Type;
use ast_factory::structs::DomainFunc;
use ast_factory::structs::Expr;
use ast_factory::structs::Trigger;
use ast_factory::structs::Location;
use ast_factory::structs::LocalVarDecl;
use ast_factory::structs::Field;
use jni::objects::JObject;

impl<'a> AstFactory<'a> {
    pub fn add(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::Add, left.to_jobject(), right.to_jobject())
    }

    pub fn sub(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::Sub, left.to_jobject(), right.to_jobject())
    }

    pub fn mul(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::Mul, left.to_jobject(), right.to_jobject())
    }

    pub fn div(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::Div, left.to_jobject(), right.to_jobject())
    }

    pub fn module(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::Mod, left.to_jobject(), right.to_jobject())
    }

    pub fn lt_cmp(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::LtCmp,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn le_cmp(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::LeCmp,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn gt_cmp(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::GtCmp,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn ge_cmp(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::GeCmp,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn eq_cmp(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::EqCmp,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn ne_cmp(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::NeCmp,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn int_lit(&self, i: i64) -> Expr<'a> {
        let big_i = self.jni.new_big_int(&i);
        build_ast_node!(self, Expr, ast::IntLit, big_i)
    }

    pub fn int_lit_from_ref(&self, i: &ToString) -> Expr<'a> {
        let big_i = self.jni.new_big_int(i);
        build_ast_node!(self, Expr, ast::IntLit, big_i)
    }

    pub fn minus(&self, expr: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::Minus, expr.to_jobject())
    }

    pub fn or(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::Or, left.to_jobject(), right.to_jobject())
    }

    pub fn and(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::And, left.to_jobject(), right.to_jobject())
    }

    pub fn implies(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::Implies,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn magic_wand(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::MagicWand,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn not(&self, expr: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::Not, expr.to_jobject())
    }

    pub fn true_lit(&self) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::TrueLit)
    }

    pub fn false_lit(&self) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::FalseLit)
    }

    pub fn null_lit(&self) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::NullLit)
    }

    pub fn field_access_predicate(&self, loc: Expr, perm: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::FieldAccessPredicate,
            loc.to_jobject(),
            perm.to_jobject()
        )
    }

    pub fn predicate_access_predicate(&self, loc: Expr, perm: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::PredicateAccessPredicate,
            loc.to_jobject(),
            perm.to_jobject()
        )
    }

    pub fn inhale_exhale_pred(&self, inhale: Expr, exhale: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::InhaleExhaleExp,
            inhale.to_jobject(),
            exhale.to_jobject()
        )
    }

    pub fn wildcard_perm(&self) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::WildcardPerm)
    }

    pub fn full_perm(&self) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::FullPerm)
    }

    pub fn no_perm(&self) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::NoPerm)
    }

    pub fn epsilon_perm(&self) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::EpsilonPerm)
    }

    pub fn fractional_perm(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::FractionalPerm,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn perm_div(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::PermDiv,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn current_perm(&self, loc: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::CurrentPerm, loc.to_jobject())
    }

    pub fn perm_minus(&self, expr: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::PermMinus, expr.to_jobject())
    }

    pub fn perm_add(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::PermAdd,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn perm_sub(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::PermSub,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn perm_mul(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::PermMul,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn int_perm_mul(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::IntPermMul,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn perm_lt_cmp(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::PermLtCmp,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn perm_le_cmp(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::PermLeCmp,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn perm_gt_cmp(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::PermGtCmp,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn perm_ge_cmp(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::PermGeCmp,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn func_app(&self, function_name: &str, args: &[Expr], formal_args: &[LocalVarDecl], return_type: Type) -> Expr<'a> {
        let func_app_wrapper = ast::FuncApp::with(self.env);
        let obj = self.jni.unwrap_result(func_app_wrapper.call_apply(
            self.jni.new_string(function_name),
            self.jni.new_seq(&map_to_jobjects!(args)),
            self.no_position().to_jobject(),
            self.no_info(),
            return_type.to_jobject(),
            self.jni.new_seq(&map_to_jobjects!(formal_args)),
            self.no_trafos()
        ));
        Expr::new(obj)
    }

    pub fn domain_func_app(
        &self,
        domain_func: DomainFunc,
        args: &[Expr],
        type_var_map: &[(Type, Type)],
    ) -> Expr<'a> {
        let domain_func_app_object_wrapper = ast::DomainFuncApp_object::with(self.env);
        let obj = self.jni.unwrap_result(
            domain_func_app_object_wrapper.call_apply(
                self.jni
                    .unwrap_result(domain_func_app_object_wrapper.singleton()),
                domain_func.to_jobject(),
                self.jni.new_seq(&map_to_jobjects!(args)),
                self.jni.new_map(&map_to_jobject_pairs!(type_var_map)),
                self.no_position().to_jobject(),
                self.no_info(),
                self.no_trafos(),
            ),
        );
        Expr::new(obj)
    }

    pub fn field_access(&self, rcv: Expr, field: Field) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::FieldAccess,
            rcv.to_jobject(),
            field.to_jobject()
        )
    }

    pub fn predicate_access(&self, args: &[Expr], predicate_name: &str) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::PredicateAccess,
            self.jni.new_seq(&map_to_jobjects!(args)),
            self.jni.new_string(predicate_name)
        )
    }

    pub fn cond_exp(&self, cond: Expr, then_expr: Expr, else_expr: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::CondExp,
            cond.to_jobject(),
            then_expr.to_jobject(),
            else_expr.to_jobject()
        )
    }

    pub fn unfolding(&self, acc: Expr, body: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::Unfolding,
            acc.to_jobject(),
            body.to_jobject()
        )
    }

    pub fn applying(&self, wand: Expr, body: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::Applying,
            wand.to_jobject(),
            body.to_jobject()
        )
    }

    pub fn old(&self, expr: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::Old, expr.to_jobject())
    }

    pub fn labelled_old(&self, expr: Expr, old_label: &str) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::LabelledOld,
            expr.to_jobject(),
            self.jni.new_string(old_label)
        )
    }

    pub fn let_expr(&self, variable: LocalVarDecl, expr: Expr, body: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::Let,
            variable.to_jobject(),
            expr.to_jobject(),
            body.to_jobject()
        )
    }

    pub fn forall(&self, variables: &[LocalVarDecl], triggers: &[Trigger], expr: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::Forall,
            self.jni.new_seq(&map_to_jobjects!(variables)),
            self.jni.new_seq(&map_to_jobjects!(triggers)),
            expr.to_jobject()
        )
    }

    pub fn exists(&self, variables: &[LocalVarDecl], expr: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::Exists,
            self.jni.new_seq(&map_to_jobjects!(variables)),
            expr.to_jobject()
        )
    }

    pub fn for_perm(
        &self,
        variable: LocalVarDecl,
        access_list: &[Location],
        body: Expr,
    ) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::ForPerm,
            variable.to_jobject(),
            self.jni.new_seq(&map_to_jobjects!(access_list)),
            body.to_jobject()
        )
    }

    pub fn trigger(&self, exps: &[Expr]) -> Trigger<'a> {
        build_ast_node!(
            self,
            Trigger,
            ast::Trigger,
            self.jni.new_seq(&map_to_jobjects!(exps))
        )
    }

    pub fn local_var(&self, name: &str, var_type: Type) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::LocalVar,
            self.jni.new_string(name),
            var_type.to_jobject()
        )
    }

    pub fn result(&self, var_type: Type) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::Result, var_type.to_jobject())
    }

    pub fn empty_seq(&self, elem_type: Type) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::EmptySeq, elem_type.to_jobject())
    }

    pub fn explicit_seq(&self, elems: &[Expr]) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::ExplicitSeq,
            self.jni.new_seq(&map_to_jobjects!(elems))
        )
    }

    pub fn range_seq(&self, low: Expr, high: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::RangeSeq,
            low.to_jobject(),
            high.to_jobject()
        )
    }

    pub fn seq_append(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::SeqAppend,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn seq_index(&self, seq: Expr, index: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::SeqIndex,
            seq.to_jobject(),
            index.to_jobject()
        )
    }

    pub fn seq_take(&self, seq: Expr, num: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::SeqTake, seq.to_jobject(), num.to_jobject())
    }

    pub fn seq_drop(&self, seq: Expr, num: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::SeqDrop, seq.to_jobject(), num.to_jobject())
    }

    pub fn seq_contains(&self, elem: Expr, seq: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::SeqContains,
            elem.to_jobject(),
            seq.to_jobject()
        )
    }

    pub fn seq_update(&self, seq: Expr, index: Expr, elem: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::SeqUpdate,
            seq.to_jobject(),
            index.to_jobject(),
            elem.to_jobject()
        )
    }

    pub fn seq_length(&self, seq: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::SeqLength, seq.to_jobject())
    }

    pub fn empty_set(&self, elem_type: Type) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::EmptySet, elem_type.to_jobject())
    }

    pub fn explicit_set(&self, elems: &[Expr]) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::ExplicitSet,
            self.jni.new_seq(&map_to_jobjects!(elems))
        )
    }

    pub fn empty_multiset(&self, elem_type: Type) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::EmptyMultiset, elem_type.to_jobject())
    }

    pub fn explicit_multiset(&self, elems: &[Expr]) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::ExplicitMultiset,
            self.jni.new_seq(&map_to_jobjects!(elems))
        )
    }

    pub fn any_set_union(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::AnySetUnion,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn any_set_intersection(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::AnySetIntersection,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn any_set_subset(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::AnySetSubset,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn any_set_minus(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::AnySetMinus,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn any_set_contains(&self, elem: Expr, set: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::AnySetContains,
            elem.to_jobject(),
            set.to_jobject()
        )
    }

    pub fn any_set_cardinality(&self, set: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::AnySetCardinality, set.to_jobject())
    }

    pub fn simplified_expression(&self, expr: Expr) -> Expr<'a> {
        let simplifier_object_wrapper = ast::utility::Simplifier_object::with(self.env);
        let obj = self.jni.unwrap_result(
            simplifier_object_wrapper.call_simplify(
                self.jni
                    .unwrap_result(simplifier_object_wrapper.singleton()),
                expr.to_jobject()
            ),
        );
        Expr::new(obj)
    }
}
