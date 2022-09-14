use egg::{define_language, Id, Symbol};

define_language! {
    pub(super) enum ExpressionLanguage {
        "true" = True,
        "false" = False,
        "NON_ALIASED_ADDRESS" = NonAliasedAddress,
        "==" = EqCmp([Id; 2]),
        "!=" = NeCmp([Id; 2]),
        ">" = GtCmp([Id; 2]),
        ">=" = GeCmp([Id; 2]),
        "<=" = LtCmp([Id; 2]),
        "<" = LeCmp([Id; 2]),
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        "/" = Div([Id; 2]),
        "%" = Mod([Id; 2]),
        "&&" = And([Id; 2]),
        "||" = Or([Id; 2]),
        "==>" = Implies([Id; 2]),
        "!" = Not(Id),
        "neg" = Minus(Id),
        Int(i64),
        BigInt(Symbol),
        Variable(Symbol),
        FuncApp(Symbol, Vec<Id>),
        BuiltinFuncApp(Symbol, Vec<Id>),
    }
}
