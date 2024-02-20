use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::{BTreeMap, BTreeSet};
use vir_crate::{
    common::{
        expression::{
            BinaryOperationHelpers, ExpressionIterator, QuantifierHelpers, UnaryOperationHelpers,
        },
        graphviz::ToGraphviz,
    },
    low::{
        self as vir_low,
        ast::statement::visitors::StatementFolder,
        expression::visitors::{default_fold_container_op, ExpressionFolder},
        operations::ty::Typed,
        ty::visitors::TypeFolder,
    },
};

pub(crate) fn desugar_containers(
    source_filename: &str,
    mut program: vir_low::Program,
) -> vir_low::Program {
    let mut rewriter = Rewriter {
        used_set_types: FxHashSet::default(),
        used_set_constructors: FxHashSet::default(),
    };
    for procedure in &mut program.procedures {
        desugar_containers_in_procedure(&mut rewriter, procedure);
        if prusti_common::config::dump_debug_info() {
            prusti_common::report::log::report_with_writer(
                "graphviz_method_vir_low_after_desugar_containers",
                format!("{}.{}.dot", source_filename, procedure.name),
                |writer| procedure.to_graphviz(writer).unwrap(),
            );
        }
    }
    for domain in &mut program.domains {
        desugar_containers_in_domain(&mut rewriter, domain);
    }
    for ty in rewriter.used_set_types {
        let domain_name = set_domain_name(&ty);
        let mut functions = Vec::new();
        let mut axioms = Vec::new();
        let set_contains_function_name = vir_low::ContainerOpKind::SetContains.to_string();
        let set_subset_function_name = vir_low::ContainerOpKind::SetSubset.to_string();
        for (container_type, arity) in &rewriter.used_set_constructors {
            let vir_low::Type::Set(set_type) = container_type else {
                unreachable!();
            };
            if &ty != set_type {
                continue;
            }
            let function_name = format!("SetConstructor{}", arity);
            let mut parameters = Vec::new();
            let mut contained_conjuncts = Vec::new();
            for i in 0..*arity {
                let parameter = vir_low::VariableDecl {
                    name: format!("_{}", i),
                    ty: (*ty.element_type).clone(),
                };
                parameters.push(parameter);
            }
            let return_type = vir_low::Type::Set(ty.clone());
            let constructor_call = vir_low::Expression::domain_function_call(
                domain_name.clone(),
                function_name.clone(),
                parameters
                    .clone()
                    .into_iter()
                    .map(vir_low::Expression::local_no_pos)
                    .collect(),
                return_type.clone(),
            );
            for parameter in &parameters {
                contained_conjuncts.push(vir_low::Expression::domain_function_call(
                    domain_name.clone(),
                    set_contains_function_name.clone(),
                    vec![
                        vir_low::Expression::local_no_pos(parameter.clone()),
                        constructor_call.clone(),
                    ],
                    vir_low::Type::Bool,
                ));
            }
            let function = vir_low::DomainFunctionDecl {
                name: function_name.clone(),
                is_unique: false,
                parameters: parameters.clone(),
                return_type,
            };
            let arguments_contained_axiom = vir_low::DomainAxiomDecl {
                comment: None,
                name: format!("{}ArgumentsContained", function_name),
                body: vir_low::Expression::forall(
                    parameters.clone(),
                    vec![vir_low::Trigger::new(vec![constructor_call.clone()])],
                    contained_conjuncts.into_iter().conjoin(),
                ),
            };
            functions.push(function);
            axioms.push(arguments_contained_axiom);
        }
        let set_subset_function = vir_low::DomainFunctionDecl {
            name: set_subset_function_name.clone(),
            is_unique: false,
            parameters: vec![
                vir_low::VariableDecl {
                    name: "set1".to_string(),
                    ty: vir_low::Type::Set(ty.clone()),
                },
                vir_low::VariableDecl {
                    name: "set2".to_string(),
                    ty: vir_low::Type::Set(ty.clone()),
                },
            ],
            return_type: vir_low::Type::Bool,
        };
        functions.push(set_subset_function);
        {
            let set_a = vir_low::VariableDecl {
                name: "set1".to_string(),
                ty: vir_low::Type::Set(ty.clone()),
            };
            let set_b = vir_low::VariableDecl {
                name: "set2".to_string(),
                ty: vir_low::Type::Set(ty.clone()),
            };
            let element = vir_low::VariableDecl {
                name: "element".to_string(),
                ty: (*ty.element_type).clone(),
            };
            let set_a_contains_element = vir_low::Expression::domain_function_call(
                domain_name.clone(),
                set_contains_function_name.clone(),
                vec![
                    vir_low::Expression::local_no_pos(element.clone()),
                    vir_low::Expression::local_no_pos(set_a.clone()),
                ],
                vir_low::Type::Bool,
            );
            let set_b_contains_element = vir_low::Expression::domain_function_call(
                domain_name.clone(),
                set_contains_function_name.clone(),
                vec![
                    vir_low::Expression::local_no_pos(element.clone()),
                    vir_low::Expression::local_no_pos(set_b.clone()),
                ],
                vir_low::Type::Bool,
            );
            let elements_contained = vir_low::Expression::forall(
                vec![element.clone()],
                vec![
                    vir_low::Trigger::new(vec![set_a_contains_element.clone()]),
                    vir_low::Trigger::new(vec![set_b_contains_element.clone()]),
                ],
                vir_low::Expression::implies(
                    set_a_contains_element.clone(),
                    set_b_contains_element.clone(),
                ),
            );
            let set_a_b_subset = vir_low::Expression::domain_function_call(
                domain_name.clone(),
                set_subset_function_name.clone(),
                vec![
                    vir_low::Expression::local_no_pos(set_a.clone()),
                    vir_low::Expression::local_no_pos(set_b.clone()),
                ],
                vir_low::Type::Bool,
            );
            let set_subset = vir_low::Expression::forall(
                vec![set_a.clone(), set_b.clone()],
                vec![vir_low::Trigger::new(vec![set_a_b_subset.clone()])],
                vir_low::Expression::equals(set_a_b_subset.clone(), elements_contained.clone()),
            );
            let set_subset_axiom = vir_low::DomainAxiomDecl {
                comment: None,
                name: "SetSubset".to_string(),
                body: set_subset,
            };
            axioms.push(set_subset_axiom);
        }
        let set_contains_function = vir_low::DomainFunctionDecl {
            name: set_contains_function_name.clone(),
            is_unique: false,
            parameters: vec![
                vir_low::VariableDecl {
                    name: "element".to_string(),
                    ty: (*ty.element_type).clone(),
                },
                vir_low::VariableDecl {
                    name: "set".to_string(),
                    ty: vir_low::Type::Set(ty.clone()),
                },
            ],
            return_type: vir_low::Type::Bool,
        };
        functions.push(set_contains_function);
        let domain = vir_low::DomainDecl {
            name: domain_name.clone(),
            functions,
            axioms,
            rewrite_rules: Vec::new(),
        };
        program.domains.push(domain);
    }
    program
}

fn desugar_containers_in_procedure(
    rewriter: &mut Rewriter,
    procedure: &mut vir_low::ProcedureDecl,
) {
    for basic_block in procedure.basic_blocks.values_mut() {
        for statement in std::mem::take(&mut basic_block.statements) {
            let new_statement = rewriter.fold_statement(statement);
            basic_block.statements.push(new_statement);
        }
    }
}

fn desugar_containers_in_domain(rewriter: &mut Rewriter, domain: &mut vir_low::DomainDecl) {
    for mut function in std::mem::take(&mut domain.functions) {
        function.return_type = TypeFolder::fold_type(rewriter, function.return_type);
        for mut parameter in std::mem::take(&mut function.parameters) {
            parameter.ty = TypeFolder::fold_type(rewriter, parameter.ty);
            function.parameters.push(parameter);
        }
        domain.functions.push(function);
    }
    for mut axiom in std::mem::take(&mut domain.axioms) {
        axiom.body = ExpressionFolder::fold_expression(rewriter, axiom.body);
        domain.axioms.push(axiom);
    }
}

struct Rewriter {
    used_set_types: FxHashSet<vir_low::ty::Set>,
    used_set_constructors: FxHashSet<(vir_low::Type, usize)>,
}

impl StatementFolder for Rewriter {
    fn fold_expression(&mut self, expression: vir_low::Expression) -> vir_low::Expression {
        ExpressionFolder::fold_expression(self, expression)
    }
}

impl ExpressionFolder for Rewriter {
    fn fold_type(&mut self, ty: vir_low::Type) -> vir_low::Type {
        TypeFolder::fold_type(self, ty)
    }
    fn fold_trigger(&mut self, mut trigger: vir_low::Trigger) -> vir_low::Trigger {
        for term in std::mem::take(&mut trigger.terms) {
            let new_term = ExpressionFolder::fold_expression(self, term);
            trigger.terms.push(new_term);
        }
        trigger
    }
    fn fold_container_op_enum(
        &mut self,
        container_op: vir_low::ContainerOp,
    ) -> vir_low::Expression {
        let function_name = match container_op.kind {
            vir_low::ContainerOpKind::SeqConstructor => todo!(),
            vir_low::ContainerOpKind::SetConstructor => {
                self.used_set_constructors.insert((
                    container_op.container_type.clone(),
                    container_op.operands.len(),
                ));
                format!("SetConstructor{}", container_op.operands.len())
            }
            vir_low::ContainerOpKind::MultiSetConstructor => todo!(),
            _ => container_op.kind.to_string(),
        };
        let container_op = default_fold_container_op(self, container_op);
        // This is already the converterd type.
        let return_type = container_op.get_type().clone();
        let vir_low::Type::Domain(domain) = &container_op.container_type else {
            unreachable!();
        };
        let domain_name = domain.name.clone();
        vir_low::Expression::domain_function_call(
            domain_name,
            function_name,
            container_op.operands,
            return_type,
        )
    }
}

impl TypeFolder for Rewriter {
    fn fold_type(&mut self, ty: vir_low::Type) -> vir_low::Type {
        match ty {
            vir_low::Type::Seq(container) => unimplemented!(),
            vir_low::Type::Set(mut container) => {
                self.used_set_types.insert(container.clone());
                container.element_type = TypeFolder::fold_type_boxed(self, container.element_type);
                let new_type = set_domain(&container);
                new_type
            }
            vir_low::Type::MultiSet(container) => unimplemented!(),
            vir_low::Type::Map(container) => unimplemented!(),
            _ => ty,
        }
    }
}

fn domain_name(container: &vir_low::Type) -> String {
    match container {
        // vir_low::Type::Seq(container) => seq_domain_name(container),
        vir_low::Type::Set(container) => set_domain_name(container),
        // vir_low::Type::MultiSet(container) => multi_set_domain_name(container),
        // vir_low::Type::Map(container) => map_domain_name(container),
        _ => unimplemented!("domain_name for {}", container),
    }
}

fn set_domain_name(container: &vir_low::ty::Set) -> String {
    let vir_low::Type::Domain(element_domain) = &*container.element_type else {
        unreachable!("Set element type is not a domain type. It is: {}", container.element_type);
    };
    let domain_name = format!("Set<{}>", element_domain.name);
    debug_assert!(!domain_name.contains(' '));
    domain_name
}

fn set_domain(container: &vir_low::ty::Set) -> vir_low::Type {
    let domain_name = set_domain_name(container);
    vir_low::Type::domain(domain_name)
}
