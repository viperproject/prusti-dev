use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::{BTreeMap, BTreeSet};
use vir_crate::{
    common::{expression::UnaryOperationHelpers, graphviz::ToGraphviz},
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
        used_container_types: FxHashSet::default(),
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
    program
}

fn desugar_containers_in_procedure(
    rewriter: &mut Rewriter,
    procedure: &mut vir_low::ProcedureDecl,
) {
    for basic_block in procedure.basic_blocks.values_mut() {
        let mut new_statements = Vec::new();
        for statement in std::mem::take(&mut basic_block.statements) {
            let new_statement = rewriter.fold_statement(statement);
            new_statements.push(new_statement);
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
    used_container_types: FxHashSet<vir_low::Type>,
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
        let container_op = default_fold_container_op(self, container_op);
        // This is already the converterd type.
        let return_type = container_op.get_type().clone();
        let vir_low::Type::Domain(domain) = &container_op.container_type else {
            unreachable!();
        };
        let domain_name = domain.name.clone();
        vir_low::Expression::domain_function_call(
            domain_name,
            container_op.kind.to_string(),
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
                self.used_container_types.insert((*container.element_type).clone());
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
    let domain_name = format!("Set<{}>", container.element_type);
    debug_assert!(!domain_name.contains(' '));
    domain_name
}

fn set_domain(container: &vir_low::ty::Set) -> vir_low::Type {
    let domain_name = set_domain_name(container);
    vir_low::Type::domain(domain_name)
}
