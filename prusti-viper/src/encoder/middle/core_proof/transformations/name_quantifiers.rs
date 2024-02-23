use vir_crate::low::{
    self as vir_low,
    ast::statement::visitors::StatementFolder,
    expression::visitors::{default_fold_quantifier, ExpressionFolder},
};

pub(crate) fn name_quantifiers(
    _source_filename: &str,
    mut program: vir_low::Program,
) -> vir_low::Program {
    for domain in &mut program.domains {
        for axiom in std::mem::take(&mut domain.axioms) {
            let axiom = name_quantifiers_in_axiom(&domain.name, axiom);
            domain.axioms.push(axiom);
        }
    }
    // for procedure in &mut program.procedures{
    //     let procedure = expand_quantifiers_in_procedure(procedure);
    //     program.procedures.push(procedure);
    // }
    program
}

fn name_quantifiers_in_axiom(
    domain_name: &str,
    mut axiom: vir_low::DomainAxiomDecl,
) -> vir_low::DomainAxiomDecl {
    let mut namer = QuantifierNamer {
        base_name: format!("{}${}", domain_name, axiom.name),
        counter: 0,
    };
    axiom.body = ExpressionFolder::fold_expression(&mut namer, axiom.body);
    axiom
}

struct QuantifierNamer {
    base_name: String,
    counter: usize,
}

impl ExpressionFolder for QuantifierNamer {
    fn fold_quantifier(&mut self, quantifier: vir_low::Quantifier) -> vir_low::Quantifier {
        let mut quantifier = default_fold_quantifier(self, quantifier);
        if quantifier.name.is_none() {
            quantifier.name = Some(format!("{}${}", self.base_name, self.counter));
            self.counter += 1;
        }
        quantifier
    }
}

impl StatementFolder for QuantifierNamer {
    fn fold_expression(&mut self, expression: vir_low::Expression) -> vir_low::Expression {
        ExpressionFolder::fold_expression(self, expression)
    }
}
