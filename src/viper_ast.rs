use jni::JNIEnv;
use jni::objects::JObject;
use jni::objects::JValue;
use jni::errors::Error;

// Offer wrapper functions around the Viper AST node constructors that we use
// (structures like Program and Function, types like SetType, expressions like
// FalseLit, statements like While, and some other stuff)

pub_scala_object_getter!(
    get_quantified_permissions,
    "viper/silver/ast/utility/QuantifiedPermissions"
);
pub_scala_object_getter!(get_add_op, "viper/silver/ast/AddOp");
pub_scala_object_getter!(get_div_op, "viper/silver/ast/DivOp");
pub_scala_object_getter!(get_frac_op, "viper/silver/ast/FracOp");
pub_scala_object_getter!(get_ge_op, "viper/silver/ast/GeOp");
pub_scala_object_getter!(get_gt_op, "viper/silver/ast/GtOp");
pub_scala_object_getter!(get_implies_op, "viper/silver/ast/ImpliesOp");
pub_scala_object_getter!(get_int_perm_mul_op, "viper/silver/ast/IntPermMulOp");
pub_scala_object_getter!(get_le_op, "viper/silver/ast/LeOp");
pub_scala_object_getter!(get_lt_op, "viper/silver/ast/LtOp");
pub_scala_object_getter!(get_mod_op, "viper/silver/ast/ModOp");
pub_scala_object_getter!(get_mul_op, "viper/silver/ast/MulOp");
pub_scala_object_getter!(get_neg_op, "viper/silver/ast/NegOp");
pub_scala_object_getter!(get_not_op, "viper/silver/ast/NotOp");
pub_scala_object_getter!(get_or_op, "viper/silver/ast/OrOp");
pub_scala_object_getter!(get_perm_add_op, "viper/silver/ast/PermAddOp");
pub_scala_object_getter!(get_perm_div_op, "viper/silver/ast/PermDivOp");
pub_scala_object_getter!(get_sub_op, "viper/silver/ast/SubOp");
pub_scala_object_getter!(get_no_position, "viper/silver/ast/NoPosition");
pub_scala_object_getter!(get_no_info, "viper/silver/ast/NoInfo");
pub_scala_object_getter!(get_no_trafos, "viper/silver/ast/NoTrafos");
pub_scala_object_getter!(get_int, "viper/silver/ast/Int");
pub_scala_object_getter!(get_bool, "viper/silver/ast/Bool");
pub_scala_object_getter!(get_ref, "viper/silver/ast/Ref");
pub_scala_object_getter!(get_perm, "viper/silver/ast/Perm");

// fn function_domain_type(self):
// fn empty_seq(self):
// fn singleton_seq(self, element):
// fn append(self, list, to_append):
// fn to_seq(self, list):
// fn to_list(self, seq):
// fn to_map(self, dict):
// fn to_big_int(self, num):
// fn Program(self, domains, fields, functions, predicates, methods, position, info):

pub_scala_object_getter!(get_program_object, "viper/silver/ast/Program");

pub fn new_program<'a>(
    env: &'a JNIEnv,
    program_object: JObject,
    domains: JObject,
    fields: JObject,
    functions: JObject,
    predicates: JObject,
    methods: JObject,
    position: JObject,
    info: JObject,
    errt: JObject,
) -> Result<JObject<'a>, Error> {
    env.call_method(
        program_object,
        "apply",
        "(\
            Lscala/collection/Seq;\
            Lscala/collection/Seq;\
            Lscala/collection/Seq;\
            Lscala/collection/Seq;\
            Lscala/collection/Seq;\
            Lviper/silver/ast/Position;\
            Lviper/silver/ast/Info;\
            Lviper/silver/ast/ErrorTrafo;\
        )\
        Lviper/silver/ast/Program;",
        &[
            JValue::Object(domains),
            JValue::Object(fields),
            JValue::Object(functions),
            JValue::Object(predicates),
            JValue::Object(methods),
            JValue::Object(position),
            JValue::Object(info),
            JValue::Object(errt),
        ],
    ).and_then(|x| x.l())
}

// fn Function(self, name, args, type, pres, posts, body, position, info):
// fn Method(self, name, args, returns, pres, posts, locals, body, position, info):
// fn Field(self, name, type, position, info):
// fn Predicate(self, name, args, body, position, info):
// fn PredicateAccess(self, args, pred_name, position, info):
// fn PredicateAccessPredicate(self, loc, perm, position, info):
// fn Fold(self, predicate, position, info):
// fn Unfold(self, predicate, position, info):
// fn Unfolding(self, predicate, expr, position, info):
// fn SeqType(self, element_type):
// fn SetType(self, element_type):
// fn Domain(self, name, functions, axioms, typevars, position, info):
// fn DomainFunc(self, name, args, type, unique, position, info, domain_name):
// fn DomainAxiom(self, name, expr, position, info, domain_name):
// fn DomainType(self, name, type_vars_map, type_vars):
// fn DomainFuncApp(self, func_name, args, type_passed, position, info, domain_name, type_var_map={}):
// fn TypeVar(self, name):
// fn MethodCall(self, method_name, args, targets, position, info):
// fn NewStmt(self, lhs, fields, position, info):
// fn Label(self, name, position, info):
// fn Goto(self, name, position, info):
// fn Seqn(self, body, position, info, locals=[]):
// fn LocalVarAssign(self, lhs, rhs, position, info):
// fn FieldAssign(self, lhs, rhs, position, info):
// fn FieldAccess(self, receiver, field, position, info):
// fn FieldAccessPredicate(self, fieldacc, perm, position, info):
// fn Old(self, expr, position, info):
// fn Inhale(self, expr, position, info):
// fn Exhale(self, expr, position, info):
// fn InhaleExhaleExp(self, inhale, exhale, position, info):
// fn Assert(self, expr, position, info):
// fn FullPerm(self, position, info):
// fn NoPerm(self, position, info):
// fn WildcardPerm(self, position, info):
// fn FractionalPerm(self, left, right, position, info):
// fn CurrentPerm(self, location, position, info):
// fn ForPerm(self, variable, access_list, body, position, info):
// fn PermMinus(self, exp, position, info):
// fn PermAdd(self, left, right, position, info):
// fn PermSub(self, left, right, position, info):
// fn PermMul(self, left, right, position, info):
// fn IntPermMul(self, left, right, position, info):
// fn PermLtCmp(self, left, right, position, info):
// fn PermLeCmp(self, left, right, position, info):
// fn PermGtCmp(self, left, right, position, info):
// fn PermGeCmp(self, left, right, position, info):
// fn Not(self, expr, position, info):
// fn Minus(self, expr, position, info):
// fn CondExp(self, cond, then, els, position, info):
// fn EqCmp(self, left, right, position, info):
// fn NeCmp(self, left, right, position, info):
// fn GtCmp(self, left, right, position, info):
// fn GeCmp(self, left, right, position, info):
// fn LtCmp(self, left, right, position, info):
// fn LeCmp(self, left, right, position, info):
// fn IntLit(self, num, position, info):
// fn Implies(self, left, right, position, info):
// fn FuncApp(self, name, args, position, info, type, formalargs):
// fn ExplicitSeq(self, elems, position, info):
// fn ExplicitSet(self, elems, position, info):
// fn EmptySeq(self, type, position, info):
// fn EmptySet(self, type, position, info):
// fn LocalVarDecl(self, name, type, position, info):
// fn LocalVar(self, name, type, position, info):
// fn Result(self, type, position, info):
// fn AnySetContains(self, elem, s, position, info):
// fn AnySetUnion(self, left, right, position, info):
// fn SeqAppend(self, left, right, position, info):
// fn SeqContains(self, elem, s, position, info):
// fn SeqLength(self, s, position, info):
// fn SeqIndex(self, s, ind, position, info):
// fn SeqTake(self, s, end, position, info):
// fn SeqDrop(self, s, end, position, info):
// fn Add(self, left, right, position, info):
// fn Sub(self, left, right, position, info):
// fn Mul(self, left, right, position, info):
// fn Div(self, left, right, position, info):
// fn Mod(self, left, right, position, info):
// fn And(self, left, right, position, info):
// fn Or(self, left, right, position, info):
// fn If(self, cond, thn, els, position, info):
// fn TrueLit(self, position, info):
// fn FalseLit(self, position, info):
// fn NullLit(self, position, info):
// fn Forall(self, variables, triggers, exp, position, info):
// fn Exists(self, variables, exp, position, info):
// fn Trigger(self, exps, position, info):
// fn While(self, cond, invariants, locals, body, position, info):
// fn Let(self, variable, exp, body, position, info):
// fn from_option(self, option):
// fn to_function0(self, func):
// fn SimpleInfo(self, comments):
// fn to_position(self, expr, vias, error_string: str=None, rules: Rules=None, file: str = None):
