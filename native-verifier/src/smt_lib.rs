use crate::optimization::optimize_statements;

use super::{
    fol::{vir_to_fol, FolStatement},
    theory_provider::*,
};
use lazy_static::lazy_static;
use log::warn;
use regex::Regex;
use std::collections::{HashMap, HashSet};
use vir::{
    common::position::Positioned,
    low::{
        ast::{expression::*, ty::*},
        operations::ty::Typed,
        *,
    },
};

lazy_static! {
    static ref ONE_PARAM_RE: Regex = Regex::new(r"(Set|Seq|MultiSet)<([^>]+)>").unwrap();
    static ref TWO_PARAM_RE: Regex = Regex::new(r"Map<([^>]+)\s*,\s*([^>]+)>").unwrap();
    static ref MARKER_RE: Regex = Regex::new(r"label.*\$marker\b\s").unwrap();
}

const NO_Z3_PREAMBLE: &str = include_str!("theories/Preamble.smt2");
const Z3_PREAMBLE: &str = include_str!("theories/PreambleZ3.smt2");

pub struct SMTLib {
    sort_decls: Vec<String>,
    func_decls: Vec<String>,
    code: Vec<String>,
    methods: HashMap<String, MethodDecl>,
    blocks: HashMap<String, BasicBlock>,
    using_z3: bool,
}

impl SMTLib {
    pub fn new(using_z3: bool) -> Self {
        Self {
            sort_decls: Vec::new(),
            func_decls: Vec::new(),
            code: Vec::new(),
            methods: HashMap::new(),
            blocks: Default::default(),
            using_z3,
        }
    }
    fn add_sort_decl(&mut self, sort_decl: String) {
        self.sort_decls
            .push(format!("(declare-sort {} 0)", sort_decl));
    }
    fn add_func(&mut self, func_decl: String) {
        self.func_decls.push(func_decl);
    }
    fn add_assert(&mut self, assert: String) {
        self.code.push(format!("(assert {})", assert));
    }
    fn add_code(&mut self, text: String) {
        self.code.push(text);
    }
    fn emit(&mut self, predicate: FolStatement) {
        match predicate {
            FolStatement::Comment(comment) => self.add_code(format!("; {}", comment)),
            FolStatement::Assume(expression) => {
                // assert predicate
                self.add_code(format!("(assert {})", expression.to_smt()));
            }
            FolStatement::Assert { expression, reason } => {
                let position = expression.position();

                if position.id == 0 {
                    return;
                }

                // negate predicate
                let negated = Expression::UnaryOp(UnaryOp {
                    op_kind: UnaryOpKind::Not,
                    argument: Box::new(expression.clone()),
                    position,
                });

                // assert negated predicate
                self.add_code("(push)".to_string());
                self.add_code(format!("(assert {})", negated.to_smt()));
                if let Some(res) = reason {
                    self.add_code(format!(
                        "(echo \"position: {}, reason: {}\")",
                        position.id, res.id
                    ));
                } else {
                    self.add_code(format!("(echo \"position: {}\")", position.id));
                }

                self.add_code("(check-sat)".to_string());
                self.add_code("(pop)".to_string());

                // assume predicate afterwards
                self.add_code(format!(
                    "(assert {}) ; assumed after assert\n",
                    expression.to_smt()
                ));
            }
        }
    }
    fn follow(&mut self, block_label: &String, precond: Option<&Expression>) {
        let block = self
            .blocks
            .get(block_label)
            .expect("Block not found")
            .clone();

        if block.statements.is_empty() {
            return;
        }

        let is_branch = precond.is_some();

        self.add_code(format!("; Basic block: {}", block.label));
        if is_branch {
            self.add_code("(push)".to_string());
        }

        // assume precond if any
        if let Some(precond) = precond {
            // TODO: Location of the call site
            self.add_code("; Branch precond:".to_string());
            self.add_assert(precond.to_smt());
        }

        // verify body
        let predicates = vir_to_fol(&block.statements, &self.methods);
        let predicates = optimize_statements(predicates);

        predicates.into_iter().for_each(|predicate| {
            self.emit(predicate);
        });

        // process successor
        match &block.successor {
            Successor::Goto(label) => {
                self.follow(&label.name, None);
            }
            Successor::GotoSwitch(mapping) => {
                // if last branch is "true", it is the "otherwise" branch
                // see: prusti-viper/src/encoder/mir/procedures/encoder/mod.rs
                let (last_expr, last_label) = mapping.iter().last().unwrap();

                if let Expression::Constant(Constant {
                    value: ConstantValue::Bool(true),
                    ..
                }) = last_expr
                {
                    // create an "and" of all negations of previous expressions
                    let and = mapping
                        .iter()
                        .take(mapping.len() - 1)
                        .map(|(expr, _)| expr)
                        .fold(None, |acc, expr| {
                            if let Some(acc) = acc {
                                Some(Expression::BinaryOp(BinaryOp {
                                    op_kind: BinaryOpKind::And,
                                    left: Box::new(acc),
                                    right: Box::new(Expression::UnaryOp(UnaryOp {
                                        op_kind: UnaryOpKind::Not,
                                        argument: Box::new(expr.clone()),
                                        position: expr.position(),
                                    })),
                                    position: expr.position(),
                                }))
                            } else {
                                Some(Expression::UnaryOp(UnaryOp {
                                    op_kind: UnaryOpKind::Not,
                                    argument: Box::new(expr.clone()),
                                    position: expr.position(),
                                }))
                            }
                        });

                    self.follow(&last_label.name, and.as_ref());
                } else {
                    self.follow(&last_label.name, Some(last_expr));
                }

                mapping
                    .iter()
                    .take(mapping.len() - 1)
                    .for_each(|(expr, label)| {
                        self.follow(&label.name, Some(expr));
                    })
            }
            Successor::Return => {}
        }

        if is_branch {
            self.add_code(format!("(pop); End basic block: {}", block.label));
        }
    }
}

impl ToString for SMTLib {
    fn to_string(&self) -> String {
        let mut result = String::new();
        result.push_str(if self.using_z3 {
            Z3_PREAMBLE
        } else {
            NO_Z3_PREAMBLE
        });
        result.push_str("\n\n");
        result.push_str(&self.sort_decls.join("\n"));
        result.push_str("\n\n");

        let mut main: String = "\n\n".to_string();
        main.push_str(&self.func_decls.join("\n"));
        main.push_str("\n\n");
        main.push_str(&self.code.join("\n"));

        // initialize the theory providers
        let set_provider = ContainerTheoryProvider::new("Set");
        let seq_provider = ContainerTheoryProvider::new("Seq");
        let multiset_provider = ContainerTheoryProvider::new("MultiSet");
        let map_provider = MapTheoryProvider::new();

        // set of seen combinations
        let mut seen = std::collections::HashSet::new();

        for cap in ONE_PARAM_RE.captures_iter(&main) {
            let container = &cap[1];
            let element_type: &str = &cap[2];

            // check if seen so far
            if seen.contains(&(container.to_string(), element_type.to_string())) {
                continue;
            }

            match container {
                "Set" => result.push_str(&set_provider.get_theory(element_type)),
                "Seq" => result.push_str(&seq_provider.get_theory(element_type)),
                "MultiSet" => result.push_str(&multiset_provider.get_theory(element_type)),
                _ => panic!("Unknown container type: {}", container),
            }

            // add the combination to the set of seen combinations
            seen.insert((container.to_string(), element_type.to_string()));
        }

        // set of seen combinations
        let mut seen = std::collections::HashSet::new();

        // same for Map in TWO_PARAM_RE
        for cap in TWO_PARAM_RE.captures_iter(&main) {
            let key_type = &cap[1];
            let value_type = &cap[2];

            // check if seen so far
            if seen.contains(&(key_type.to_string(), value_type.to_string())) {
                continue;
            }

            result.push_str(&map_provider.get_theory(key_type, value_type));

            // add the combination to the set of seen combinations
            seen.insert((key_type.to_string(), value_type.to_string()));
        }

        result.push_str(&main);

        result
            .lines()
            .filter(|&line| !MARKER_RE.is_match(line)) // TODO: SSO form for marker variables?
            .collect::<Vec<_>>()
            .join("\n")
    }
}

pub trait SMTTranslatable {
    fn build_smt(&self, _: &mut SMTLib) {
        unimplemented!()
    }
    fn to_smt(&self) -> String {
        unimplemented!()
    }
}

// args are any collection of SMTTranslatable
fn mk_app<T>(name: &String, args: &Vec<T>) -> String
where
    T: SMTTranslatable,
{
    if args.is_empty() {
        name.clone()
    } else {
        format!(
            "({} {})",
            name,
            args.iter()
                .map(|a| a.to_smt())
                .collect::<Vec<_>>()
                .join(" ")
        )
    }
}

impl SMTTranslatable for Program {
    fn build_smt(&self, smt: &mut SMTLib) {
        self.domains.iter().for_each(|d| d.build_smt(smt));
        self.methods.iter().for_each(|d| d.build_smt(smt));
        self.procedures.iter().for_each(|d| d.build_smt(smt));

        // the following are empty in vir::low + snapshot-based encoding
        assert!(self.functions.is_empty());
        assert!(self.predicates.is_empty());
    }
}

/* #region Domains */

impl SMTTranslatable for DomainDecl {
    fn build_smt(&self, smt: &mut SMTLib) {
        smt.add_sort_decl(self.name.clone());

        if !self.functions.is_empty() {
            smt.add_func(format!("; Functions for domain {}", self.name));
            self.functions.iter().for_each(|f| f.build_smt(smt));
        }

        if !self.axioms.is_empty() {
            smt.add_code(format!("; Axioms for domain {}", self.name));
            self.axioms.iter().for_each(|a| a.build_smt(smt));
        }
    }
}

impl SMTTranslatable for DomainFunctionDecl {
    // TODO: self.is_unique
    fn build_smt(&self, smt: &mut SMTLib) {
        let mut fun = String::new();

        fun.push_str(&format!("(declare-fun {} (", self.name));
        fun.push_str(
            &self
                .parameters
                .iter()
                .map(|p| p.ty.to_smt())
                .collect::<Vec<_>>()
                .join(" "),
        );
        fun.push_str(&format!(") {})", self.return_type.to_smt()));

        smt.add_func(fun);
    }
}

impl SMTTranslatable for DomainAxiomDecl {
    fn build_smt(&self, smt: &mut SMTLib) {
        if let Some(comment) = &self.comment {
            smt.add_assert(format!("; {}", comment));
        }

        smt.add_code(format!("(assert {}) ; {}", self.body.to_smt(), self.name));
    }
}

/* #endregion */

/* #region Methods and Procedures */

impl SMTTranslatable for MethodDecl {
    fn build_smt(&self, smt: &mut SMTLib) {
        // if body is None, we have a body-less method with only pre- and postconditions
        // we assume these to be correct by default and collect their signatures
        if self.body.is_none() {
            smt.methods.insert(self.name.clone(), self.clone());
        } else {
            unimplemented!("Method bodies are not yet supported");
        }
    }
}

impl SMTTranslatable for ProcedureDecl {
    fn build_smt(&self, smt: &mut SMTLib) {
        smt.add_code(format!("; Procedure {}", self.name));

        smt.add_code("(push)".to_string());

        // declare locals
        self.locals.iter().for_each(|l| l.build_smt(smt));

        // process basic blocks
        smt.blocks.clear();

        self.basic_blocks.iter().for_each(|b| {
            smt.blocks.insert(b.label.name.clone(), b.clone());
        });

        // find a starting block
        let mut start_blocks = smt.blocks.keys().collect::<HashSet<_>>();

        for block in smt.blocks.values() {
            match &block.successor {
                Successor::Goto(label) => {
                    start_blocks.remove(&label.name);
                }
                Successor::GotoSwitch(labels) => {
                    labels.iter().for_each(|(_, l)| {
                        start_blocks.remove(&l.name);
                    });
                }
                Successor::Return => {}
            }
        }

        assert!(
            start_blocks.len() == 1,
            "Expected exactly one start block, found {}",
            start_blocks.len()
        );

        let start = start_blocks.drain().next().unwrap().clone();
        smt.follow(&start, None);

        smt.add_code("(pop)".to_string());
    }
}

impl SMTTranslatable for VariableDecl {
    fn build_smt(&self, smt: &mut SMTLib) {
        smt.add_code(format!(
            "(declare-const {} {})",
            self.name,
            self.ty.to_smt()
        ));
    }
}

/* #endregion */

impl SMTTranslatable for Expression {
    fn to_smt(&self) -> String {
        match self {
            Expression::Local(local) => local.variable.name.clone(),
            Expression::Field(_) => unimplemented!(),
            Expression::LabelledOld(_) => unimplemented!("old expressions"),
            Expression::Constant(constant) => match &constant.value {
                ConstantValue::Bool(bool) => bool.to_string(),
                ConstantValue::Int(i) => {
                    if let Some(abs_val) = i.to_string().strip_prefix('-') {
                        format!("(- {})", abs_val)
                    } else {
                        i.to_string()
                    }
                }
                ConstantValue::Float32(u32) => {
                    let bits = u32.to_le_bytes();
                    let bits = bits
                        .iter()
                        .rev()
                        .map(|b| format!("{:08b}", b))
                        .collect::<Vec<_>>()
                        .join("");
                    format!(
                        "(fp #b{} #b{} #b{})",
                        &bits.chars().next().unwrap(),
                        &bits[1..=8],
                        &bits[9..=31]
                    )
                }
                ConstantValue::Float64(u64) => {
                    let bits = u64.to_le_bytes();
                    let bits = bits
                        .iter()
                        .rev()
                        .map(|b| format!("{:08b}", b))
                        .collect::<Vec<_>>()
                        .join("");
                    format!(
                        "(fp #b{} #b{} #b{})",
                        &bits.chars().next().unwrap(),
                        &bits[1..=11],
                        &bits[12..=63]
                    )
                }
                ConstantValue::BigInt(s) => {
                    if let Some(abs_val) = s.strip_prefix('-') {
                        format!("(- {})", abs_val)
                    } else {
                        s.clone()
                    }
                }
            },
            Expression::MagicWand(wand) => {
                // if left is just constant true, we can ignore it
                if let Expression::Constant(Constant {
                    value: ConstantValue::Bool(true),
                    ..
                }) = *wand.left
                {
                    format!("(=> {} {})", wand.left.to_smt(), wand.right.to_smt())
                } else {
                    unimplemented!("Non-trivial MagicWand not supported: {}", wand);
                }
            }
            Expression::PredicateAccessPredicate(_access) => {
                warn!("PredicateAccessPredicate not supported: {}", _access);
                format!(
                    "({} {})",
                    _access.name,
                    _access
                        .arguments
                        .iter()
                        .map(|x| x.to_smt())
                        .collect::<Vec<_>>()
                        .join(" ")
                )
            }
            Expression::FieldAccessPredicate(_) => unimplemented!(),
            Expression::Unfolding(_) => unimplemented!(),
            Expression::UnaryOp(unary_op) => {
                let op_smt = if unary_op.argument.get_type().is_float() {
                    FloatUnaryOpKind(unary_op.op_kind).to_smt()
                } else {
                    IntUnaryOpKind(unary_op.op_kind).to_smt()
                };

                format!("({} {})", op_smt, unary_op.argument.to_smt())
            }
            Expression::BinaryOp(binary_op) => {
                let op_smt = if let Type::Float(fsize) = binary_op.left.get_type() {
                    FloatBinaryOpKind(binary_op.op_kind, *fsize).to_smt()
                } else {
                    IntBinaryOpKind(binary_op.op_kind).to_smt()
                };

                format!(
                    "({} {} {})",
                    op_smt,
                    binary_op.left.to_smt(),
                    binary_op.right.to_smt()
                )
            }
            Expression::PermBinaryOp(perm_binary_op) => format!(
                "({} {} {})",
                perm_binary_op.op_kind.to_smt(),
                perm_binary_op.left.to_smt(),
                perm_binary_op.right.to_smt()
            ),
            Expression::ContainerOp(container_op) => container_op.to_smt(),
            Expression::Conditional(conditional) => format!(
                "(ite {} {} {})",
                conditional.guard.to_smt(),
                conditional.then_expr.to_smt(),
                conditional.else_expr.to_smt()
            ),
            // TODO: Quantifier triggers
            Expression::Quantifier(quantifier) => {
                let mut quant = String::new();

                match quantifier.kind {
                    QuantifierKind::ForAll => quant.push_str("(forall ("),
                    QuantifierKind::Exists => quant.push_str("(exists ("),
                }

                quant.push_str(
                    &quantifier
                        .variables
                        .iter()
                        .map(|v| format!("({} {})", v.name, v.ty.to_smt()))
                        .collect::<Vec<_>>()
                        .join(" "),
                );
                quant.push_str(") ");

                let triggers: Vec<_> = quantifier
                    .triggers
                    .iter()
                    .filter(|t| {
                        !t.terms
                            .iter()
                            .any(|t| matches!(t, Expression::PredicateAccessPredicate(_)))
                        // TODO: Support triggers with predicate access predicates?
                    })
                    .collect();

                if triggers.is_empty() {
                    quant.push_str(&quantifier.body.to_smt());
                    quant.push(')');
                } else {
                    // triggers are :pattern
                    quant.push_str("(! ");
                    quant.push_str(&quantifier.body.to_smt());

                    for trigger in &triggers {
                        quant.push_str(" :pattern (");

                        quant.push_str(
                            &trigger
                                .terms
                                .iter()
                                .map(|expr| expr.to_smt())
                                .collect::<Vec<_>>()
                                .join(" "),
                        );

                        quant.push(')');
                    }

                    quant.push_str("))");
                }

                quant
            }
            Expression::LetExpr(_) => unimplemented!(),
            Expression::FuncApp(func) => {
                let mut app = "(".to_string();

                app.push_str(&func.function_name);
                app.push(' ');

                app.push_str(
                    &func
                        .arguments
                        .iter()
                        .map(|arg| arg.to_smt())
                        .collect::<Vec<_>>()
                        .join(" "),
                );

                app.push(')');
                app
            }
            Expression::DomainFuncApp(domain_func_app) => {
                mk_app(&domain_func_app.function_name, &domain_func_app.arguments)
            }
            Expression::InhaleExhale(_) => unimplemented!(),
        }
    }
}

struct IntBinaryOpKind(BinaryOpKind);
struct FloatBinaryOpKind(BinaryOpKind, Float);

impl SMTTranslatable for IntBinaryOpKind {
    fn to_smt(&self) -> String {
        match self.0 {
            BinaryOpKind::EqCmp => "=",
            BinaryOpKind::NeCmp => "distinct",
            BinaryOpKind::GtCmp => ">",
            BinaryOpKind::GeCmp => ">=",
            BinaryOpKind::LtCmp => "<",
            BinaryOpKind::LeCmp => "<=",
            BinaryOpKind::Add => "+",
            BinaryOpKind::Sub => "-",
            BinaryOpKind::Mul => "*",
            BinaryOpKind::Div => "div",
            BinaryOpKind::Mod => "rust_mod",
            BinaryOpKind::And => "and",
            BinaryOpKind::Or => "or",
            BinaryOpKind::Implies => "=>",
        }
        .to_string()
    }
}

impl SMTTranslatable for FloatBinaryOpKind {
    fn to_smt(&self) -> String {
        match (self.0, self.1) {
            // BinaryOpKind::EqCmp => "fp.eq", // TODO: = in axioms, fp.eq in arithmetic?
            (BinaryOpKind::EqCmp, _) => "=",
            (BinaryOpKind::NeCmp, Float::F32) => "fp.neq32", // Not in SMT-LIB 2.6 standard, part of static preamble
            (BinaryOpKind::NeCmp, Float::F64) => "fp.neq64", // Not in SMT-LIB 2.6 standard, part of static preamble
            (BinaryOpKind::GtCmp, _) => "fp.gt",
            (BinaryOpKind::GeCmp, _) => "fp.geq",
            (BinaryOpKind::LtCmp, _) => "fp.lt",
            (BinaryOpKind::LeCmp, _) => "fp.leq",
            (BinaryOpKind::Add, _) => "fp.add roundNearestTiesToAway",
            (BinaryOpKind::Sub, _) => "fp.sub roundNearestTiesToAway",
            (BinaryOpKind::Mul, _) => "fp.mul roundNearestTiesToAway",
            (BinaryOpKind::Div, _) => "fp.div roundNearestTiesToAway",
            (BinaryOpKind::Mod, _) => "fp.rem",
            (other, _) => unreachable!("FP {}", other),
        }
        .to_string()
    }
}

impl SMTTranslatable for PermBinaryOpKind {
    fn to_smt(&self) -> String {
        match self {
            PermBinaryOpKind::Add => "+",
            PermBinaryOpKind::Sub => "-",
            PermBinaryOpKind::Mul => "*",
            PermBinaryOpKind::Div => "/",
        }
        .to_string()
    }
}

struct IntUnaryOpKind(UnaryOpKind);
struct FloatUnaryOpKind(UnaryOpKind);

impl SMTTranslatable for IntUnaryOpKind {
    fn to_smt(&self) -> String {
        match self.0 {
            UnaryOpKind::Not => "not",
            UnaryOpKind::Minus => "-",
        }
        .to_string()
    }
}

impl SMTTranslatable for FloatUnaryOpKind {
    fn to_smt(&self) -> String {
        match self.0 {
            UnaryOpKind::Not => unreachable!("FP not"),
            UnaryOpKind::Minus => "fp.neg",
        }
        .to_string()
    }
}

impl SMTTranslatable for ContainerOp {
    fn to_smt(&self) -> String {
        match &self.kind {
            ContainerOpKind::SetConstructor => {
                if self.operands.len() == 1 {
                    return format!("(Set_singleton {})", self.operands[0].to_smt());
                }

                fn recurse(set: String, arg: &Expression) -> String {
                    format!("(Set_unionone {} {})", set, arg.to_smt())
                }
                self.operands.iter().fold("Set_empty".to_string(), recurse)
            }
            ContainerOpKind::SeqConstructor => {
                if self.operands.len() == 1 {
                    return format!("(Seq_singleton {})", self.operands[0].to_smt());
                }

                fn recurse(seq: String, arg: &Expression) -> String {
                    format!("(Seq_build {} {})", seq, arg.to_smt())
                }
                self.operands.iter().fold("Seq_empty".to_string(), recurse)
            }
            kind => format!(
                "({} {})",
                kind.to_smt(),
                self.operands
                    .iter()
                    .map(|a| a.to_smt())
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
        }
    }
}

impl SMTTranslatable for ContainerOpKind {
    fn to_smt(&self) -> String {
        match self {
            ContainerOpKind::SetCardinality => "Set_card",
            ContainerOpKind::SetConstructor => "Set_singleton",
            ContainerOpKind::SetContains => "Set_in",
            ContainerOpKind::SetEmpty => "Set_empty",
            ContainerOpKind::SetIntersection => "Set_intersection",
            ContainerOpKind::SetMinus => "Set_difference",
            ContainerOpKind::SetSubset => "Set_subset",
            ContainerOpKind::SetUnion => "Set_union",

            ContainerOpKind::SeqEmpty => "Seq_empty",
            ContainerOpKind::SeqConstructor => "Seq_singleton",
            ContainerOpKind::SeqIndex => "Seq_index",
            ContainerOpKind::SeqConcat => "Seq_concat",
            ContainerOpKind::SeqLen => "Seq_length",

            x => unimplemented!("ContainerOpKind::{}::to_smt()", x),
        }
        .to_string()
    }
}

impl SMTTranslatable for Type {
    fn to_smt(&self) -> String {
        match self {
            Type::Int => "Int".to_string(),
            Type::Bool => "Bool".to_string(),
            Type::Perm => "$Perm".to_string(),
            Type::Float(float) => match float {
                Float::F32 => "Float32".to_string(),
                Float::F64 => "Float64".to_string(),
            },
            Type::BitVector(bitvec) => match bitvec {
                // TODO: Should they map to the same type?
                BitVector::Signed(size) => {
                    format!("(_ BitVec {})", size.to_smt())
                }
                BitVector::Unsigned(size) => {
                    format!("(_ BitVec {})", size.to_smt())
                }
            },
            Type::Seq(seq) => format!("Seq<{}>", seq.element_type.to_smt()),
            Type::Set(set) => format!("Set<{}>", set.element_type.to_smt()),
            Type::MultiSet(_) => unimplemented!("MultiSet"),
            Type::Map(_) => unimplemented!("Map"),
            Type::Ref => unimplemented!("Ref"),
            Type::Domain(domain) => domain.name.to_string(),
        }
    }
}

impl SMTTranslatable for BitVectorSize {
    fn to_smt(&self) -> String {
        match self {
            BitVectorSize::BV8 => "8".to_string(),
            BitVectorSize::BV16 => "16".to_string(),
            BitVectorSize::BV32 => "32".to_string(),
            BitVectorSize::BV64 => "64".to_string(),
            BitVectorSize::BV128 => "128".to_string(),
        }
    }
}
