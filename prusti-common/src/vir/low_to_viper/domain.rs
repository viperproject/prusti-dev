use super::{Context, ToViper, ToViperDecl};
use viper::{self, AstFactory};
use vir::low::{DomainAxiomDecl, DomainDecl, DomainFunctionDecl};

impl<'a, 'v> ToViper<'v, viper::Domain<'v>> for &'a DomainDecl {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Domain<'v> {
        ast.domain(
            &self.name,
            &(&self.name, &self.functions).to_viper(context, ast),
            &(&self.name, &self.axioms).to_viper(context, ast),
            &[],
        )
    }
}

impl<'a, 'v> ToViper<'v, Vec<viper::DomainFunc<'v>>> for (&'a String, &'a Vec<DomainFunctionDecl>) {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> Vec<viper::DomainFunc<'v>> {
        self.1
            .iter()
            .map(|function| (self.0, function).to_viper(context, ast))
            .collect()
    }
}

impl<'a, 'v> ToViper<'v, viper::DomainFunc<'v>> for (&'a String, &'a DomainFunctionDecl) {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::DomainFunc<'v> {
        let (domain_name, function) = self;
        ast.domain_func(
            &function.name,
            &function.parameters.to_viper_decl(context, ast),
            function.return_type.to_viper(context, ast),
            function.is_unique,
            domain_name,
        )
    }
}

impl<'a, 'v> ToViper<'v, Vec<viper::NamedDomainAxiom<'v>>>
    for (&'a String, &'a Vec<DomainAxiomDecl>)
{
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> Vec<viper::NamedDomainAxiom<'v>> {
        self.1
            .iter()
            .map(|axiom| (self.0, axiom).to_viper(context, ast))
            .collect()
    }
}

impl<'a, 'v> ToViper<'v, viper::NamedDomainAxiom<'v>> for (&'a String, &'a DomainAxiomDecl) {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::NamedDomainAxiom<'v> {
        let (domain_name, axiom) = self;
        ast.named_domain_axiom(&axiom.name, axiom.body.to_viper(context, ast), domain_name)
    }
}
