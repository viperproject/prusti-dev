#![allow(dead_code)]

use viper_sys::wrappers::viper::silver::ast;
use ast_factory::AstFactory;
use ast_factory::structs::Type;
use ast_factory::structs::Function;
use ast_factory::structs::DomainFunc;
use ast_factory::structs::Expr;
use ast_factory::structs::Trigger;
use ast_factory::structs::Location;
use ast_factory::structs::LocalVarDecl;

impl<'a> AstFactory<'a> {
    pub fn new_add(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::Add, left.to_jobject(), right.to_jobject())
    }

    pub fn new_sub(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::Sub, left.to_jobject(), right.to_jobject())
    }

    pub fn new_mul(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::Mul, left.to_jobject(), right.to_jobject())
    }

    pub fn new_div(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::Div, left.to_jobject(), right.to_jobject())
    }

    pub fn new_mod(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::Mod, left.to_jobject(), right.to_jobject())
    }

    pub fn new_lt_cmp(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::LtCmp,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn new_le_cmp(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::LeCmp,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn new_gt_cmp(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::GtCmp,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn new_ge_cmp(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::GeCmp,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn new_eq_cmp(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::EqCmp,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn new_ne_cmp(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::NeCmp,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn new_int_lit(&self, i: i32) -> Expr<'a> {
        // TODO: take a Java BigInt as parameter
        let big_i = self.jni.new_big_int(i);
        build_ast_node!(self, Expr, ast::IntLit, big_i)
    }

    pub fn new_minus(&self, expr: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::Minus, expr.to_jobject())
    }

    pub fn new_or(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::Or, left.to_jobject(), right.to_jobject())
    }

    pub fn new_and(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::And, left.to_jobject(), right.to_jobject())
    }

    pub fn new_implies(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::Implies,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn new_magic_wand(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::MagicWand,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn new_not(&self, expr: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::Not, expr.to_jobject())
    }

    pub fn new_true_lit(&self) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::TrueLit)
    }

    pub fn new_false_lit(&self) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::FalseLit)
    }

    pub fn new_null_lit(&self) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::NullLit)
    }

    pub fn new_field_access_predicate(&self, loc: Expr, perm: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::FieldAccessPredicate,
            loc.to_jobject(),
            perm.to_jobject()
        )
    }

    pub fn new_predicate_access_predicate(&self, loc: Expr, perm: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::PredicateAccessPredicate,
            loc.to_jobject(),
            perm.to_jobject()
        )
    }

    pub fn new_inhale_exhale_pred(&self, inhale: Expr, exhale: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::InhaleExhaleExp,
            inhale.to_jobject(),
            exhale.to_jobject()
        )
    }

    pub fn new_wildcard_perm(&self) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::WildcardPerm)
    }

    pub fn new_full_perm(&self) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::FullPerm)
    }

    pub fn new_no_perm(&self) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::NoPerm)
    }

    pub fn new_epsilon_perm(&self) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::EpsilonPerm)
    }

    pub fn new_fractional_perm(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::FractionalPerm,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn new_perm_div(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::PermDiv,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn new_current_perm(&self, loc: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::CurrentPerm, loc.to_jobject())
    }

    pub fn new_perm_minus(&self, expr: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::PermMinus, expr.to_jobject())
    }

    pub fn new_perm_add(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::PermAdd,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn new_perm_sub(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::PermSub,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn new_perm_mul(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::PermMul,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn new_int_perm_mul(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::IntPermMul,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn new_perm_lt_cmp(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::PermLtCmp,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn new_perm_le_cmp(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::PermLeCmp,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn new_perm_gt_cmp(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::PermGtCmp,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn new_perm_ge_cmp(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::PermGeCmp,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn new_func_app(&self, func: &Function, args: Vec<Expr>) -> Expr<'a> {
        let func_app_object_wrapper = ast::FuncApp_object::with(self.env);
        let obj = self.jni.unwrap_result(func_app_object_wrapper.call_apply_1(
            self.jni.unwrap_result(
                func_app_object_wrapper.singleton(),
            ),
            func.to_jobject(),
            self.jni.new_seq(
                map_to_jobjects!(args),
            ),
            self.new_no_position().to_jobject(),
            self.new_no_info(),
            self.new_no_trafos(),
        ));
        Expr::new(obj)
    }

    pub fn new_domain_func_app(
        &self,
        domain_func: &DomainFunc,
        args: Vec<Expr>,
        type_var_map: Vec<(Type, Type)>,
    ) -> Expr<'a> {
        let domain_func_app_object_wrapper = ast::DomainFuncApp_object::with(self.env);
        let obj = self.jni.unwrap_result(
            domain_func_app_object_wrapper.call_apply_1(
                self.jni.unwrap_result(
                    domain_func_app_object_wrapper.singleton(),
                ),
                domain_func.to_jobject(),
                self.jni.new_seq(map_to_jobjects!(args)),
                self.jni.new_map(map_to_jobject_pairs!(type_var_map)),
                self.new_no_position().to_jobject(),
                self.new_no_info(),
                self.new_no_trafos(),
            ),
        );
        Expr::new(obj)
    }

    pub fn new_field_access(&self, rcv: Expr, field: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::FieldAccess,
            rcv.to_jobject(),
            field.to_jobject()
        )
    }

    pub fn new_predicate_access(&self, args: Vec<Expr>, predicate_name: &str) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::PredicateAccess,
            self.jni.new_seq(map_to_jobjects!(args)),
            self.jni.new_string(predicate_name)
        )
    }

    pub fn new_cond_exp(&self, cond: Expr, then_expr: Expr, else_expr: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::CondExp,
            cond.to_jobject(),
            then_expr.to_jobject(),
            else_expr.to_jobject()
        )
    }

    pub fn new_unfolding(&self, acc: Expr, body: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::Unfolding,
            acc.to_jobject(),
            body.to_jobject()
        )
    }

    pub fn new_applying(&self, wand: Expr, body: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::Applying,
            wand.to_jobject(),
            body.to_jobject()
        )
    }

    pub fn new_old(&self, expr: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::Old, expr.to_jobject())
    }

    pub fn new_labelled_old(&self, expr: Expr, old_label: &str) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::LabelledOld,
            expr.to_jobject(),
            self.jni.new_string(old_label)
        )
    }

    pub fn new_let(&self, variable: LocalVarDecl, expr: Expr, body: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::Let,
            variable.to_jobject(),
            expr.to_jobject(),
            body.to_jobject()
        )
    }

    pub fn new_forall(
        &self,
        variables: Vec<LocalVarDecl>,
        triggers: Vec<Trigger>,
        expr: Expr,
    ) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::Forall,
            self.jni.new_seq(map_to_jobjects!(variables)),
            self.jni.new_seq(map_to_jobjects!(triggers)),
            expr.to_jobject()
        )
    }

    pub fn new_exists(&self, variables: Vec<LocalVarDecl>, expr: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::Exists,
            self.jni.new_seq(map_to_jobjects!(variables)),
            expr.to_jobject()
        )
    }

    pub fn new_for_perm(
        &self,
        variable: LocalVarDecl,
        access_list: Vec<Location>,
        body: Expr,
    ) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::ForPerm,
            variable.to_jobject(),
            self.jni.new_seq(
                access_list
                    .iter()
                    .map(|x| match *x {
                        Location::Predicate(ref p) => p.to_jobject(),
                        Location::Field(ref f) => f.to_jobject(),
                    })
                    .collect(),
            ),
            body.to_jobject()
        )
    }

    pub fn new_trigger(&self, exps: Vec<Expr>) -> Trigger<'a> {
        build_ast_node!(
            self,
            Trigger,
            ast::Trigger,
            self.jni.new_seq(map_to_jobjects!(exps))
        )
    }

    pub fn new_local_var(&self, name: &str, var_type: Type) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::LocalVar,
            self.jni.new_string(name),
            var_type.to_jobject()
        )
    }

    pub fn new_result(&self, var_type: Type) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::Result, var_type.to_jobject())
    }

    pub fn new_empty_seq(&self, elem_type: Type) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::EmptySeq, elem_type.to_jobject())
    }

    pub fn new_explicit_seq(&self, elems: Vec<Expr>) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::ExplicitSeq,
            self.jni.new_seq(map_to_jobjects!(elems))
        )
    }

    pub fn new_range_seq(&self, low: Expr, high: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::RangeSeq,
            low.to_jobject(),
            high.to_jobject()
        )
    }

    pub fn new_seq_append(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::SeqAppend,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn new_seq_index(&self, seq: Expr, index: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::SeqIndex,
            seq.to_jobject(),
            index.to_jobject()
        )
    }

    pub fn new_seq_take(&self, seq: Expr, num: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::SeqTake, seq.to_jobject(), num.to_jobject())
    }

    pub fn new_seq_drop(&self, seq: Expr, num: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::SeqDrop, seq.to_jobject(), num.to_jobject())
    }

    pub fn new_seq_contains(&self, elem: Expr, seq: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::SeqContains,
            elem.to_jobject(),
            seq.to_jobject()
        )
    }

    pub fn new_seq_update(&self, seq: Expr, index: Expr, elem: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::SeqUpdate,
            seq.to_jobject(),
            index.to_jobject(),
            elem.to_jobject()
        )
    }

    pub fn new_seq_length(&self, seq: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::SeqLength, seq.to_jobject())
    }


    pub fn new_empty_set(&self, elem_type: Type) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::EmptySet, elem_type.to_jobject())
    }

    pub fn new_explicit_set(&self, elems: Vec<Expr>) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::ExplicitSet,
            self.jni.new_seq(map_to_jobjects!(elems))
        )
    }

    pub fn new_empty_multi_set(&self, elem_type: Type) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::EmptyMultiset, elem_type.to_jobject())
    }

    pub fn new_explicit_multi_set(&self, elems: Vec<Expr>) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::ExplicitMultiset,
            self.jni.new_seq(map_to_jobjects!(elems))
        )
    }

    pub fn new_any_set_union(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::AnySetUnion,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn new_any_set_intersection(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::AnySetIntersection,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn new_any_set_subset(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::AnySetSubset,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn new_any_set_minus(&self, left: Expr, right: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::AnySetMinus,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn new_any_set_contains(&self, elem: Expr, set: Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::AnySetContains,
            elem.to_jobject(),
            set.to_jobject()
        )
    }

    pub fn new_any_set_cardinality(&self, set: Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::AnySetCardinality, set.to_jobject())
    }
}
