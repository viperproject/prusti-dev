use jni::JNIEnv;
use jni::objects::JValue;
use jni::errors::Error;

// Offer wrapper functions around the Viper AST node constructors that we use
// (structures like Program and Function, types like SetType, expressions like
// FalseLit, statements like While, and some other stuff) as well as some
// convenience methods for interacting with Scala from Python that, e.g.,
// convert Python lists to Scala sequences and vice versa.

fn new_add_op<'a>(env: &'a JNIEnv) -> Result<JValue<'a>, Error> {
    env.get_static_field(
        "viper/silver/ast/AddOp$",
        "MODULE$",
        "Lviper/silver/ast/AddOp$",
    )
}


// TODO: AndOp
// TODO: DivOp
// TODO: FracOp
// TODO: GeOp
// TODO: GtOp
// TODO: ImpliesOp
// TODO: IntPermMulOp
// TODO: LeOp
// TODO: LtOp
// TODO: ModOp
// TODO: MulOp
// TODO: NegOp
// TODO: NotOp
// TODO: OrOp
// TODO: PermAddOp
// TODO: PermDivOp
// TODO: SubOp
// TODO: NoPosition
// TODO: NoInfo
// TODO: NoTrafos
// TODO: Int
// TODO: Bool
// TODO: Ref
// TODO: Perm
// TODO: None
// TODO: QuantifiedPermissions


// fn function_domain_type(self):
// fn empty_seq(self):
// fn singleton_seq(self, element):
// fn append(self, list, to_append):
// fn to_seq(self, list):
// fn to_list(self, seq):
// fn to_map(self, dict):
// fn to_big_int(self, num):
// fn Program(self, domains, fields, functions, predicates, methods, position, info):
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
