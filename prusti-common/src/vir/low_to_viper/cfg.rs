use super::{Context, ToViper, ToViperDecl};
use viper::{self, AstFactory};
use vir::{
    common::cfg::Cfg,
    legacy::RETURN_LABEL,
    low::{
        ast::position::Position,
        cfg::{procedure::Successor, Label, MethodDecl, ProcedureDecl},
    },
};

impl<'a, 'v> ToViper<'v, viper::Method<'v>> for &'a ProcedureDecl {
    fn to_viper(&self, context: &mut Context<'v>, ast: &AstFactory<'v>) -> viper::Method<'v> {
        let mut statements: Vec<viper::Stmt> = vec![];
        let mut declarations: Vec<viper::Declaration> = vec![];
        for local in &self.locals {
            declarations.push(local.to_viper_decl(context, ast).into());
        }
        let traversal_order = self.get_topological_sort();
        for label in &traversal_order {
            let block = self.basic_blocks.get(label).unwrap();
            declarations.push(label.to_viper_decl(context, ast).into());
            statements.push(label.to_viper(context, ast));
            statements.extend(block.statements.to_viper(context, ast));
            statements.push(block.successor.to_viper(context, ast));
        }
        statements.push(ast.label(RETURN_LABEL, &[]));
        declarations.push(ast.label(RETURN_LABEL, &[]).into());
        for label in &self.custom_labels {
            declarations.push(label.to_viper_decl(context, ast).into());
        }
        let body = Some(ast.seqn(&statements, &declarations));
        ast.method(&self.name, &[], &[], &[], &[], body)
    }
}

impl<'v> ToViper<'v, viper::Stmt<'v>> for Successor {
    fn to_viper(&self, context: &mut Context<'v>, ast: &AstFactory<'v>) -> viper::Stmt<'v> {
        match self {
            Successor::Goto(target) => ast.goto(&target.name),
            Successor::GotoSwitch(targets) => {
                let mut statements = Vec::new();
                for (test, target) in targets {
                    let goto = ast.seqn(&[ast.goto(&target.name)], &[]);
                    let skip = ast.seqn(&[], &[]);
                    let conditional_goto = ast.if_stmt(test.to_viper(context, ast), goto, skip);
                    statements.push(conditional_goto);
                }
                let position = Position::default(); // FIXME
                let assert_false = ast.assert(
                    ast.false_lit_with_pos(position.to_viper(context, ast)),
                    position.to_viper(context, ast),
                );
                statements.push(assert_false);
                ast.seqn(&statements, &[])
            }
            Successor::Return => ast.goto(RETURN_LABEL),
        }
    }
}

impl<'v> ToViperDecl<'v, viper::Stmt<'v>> for Label {
    fn to_viper_decl(&self, _context: &mut Context<'v>, ast: &AstFactory<'v>) -> viper::Stmt<'v> {
        ast.label(&self.name, &[])
    }
}

impl<'v> ToViper<'v, viper::Stmt<'v>> for Label {
    fn to_viper(&self, _context: &mut Context<'v>, ast: &AstFactory<'v>) -> viper::Stmt<'v> {
        ast.label(&self.name, &[])
    }
}

impl<'a, 'v> ToViper<'v, viper::Method<'v>> for &'a MethodDecl {
    fn to_viper(&self, context: &mut Context<'v>, ast: &AstFactory<'v>) -> viper::Method<'v> {
        let body = self
            .body
            .as_ref()
            .map(|statements| ast.seqn(&statements.to_viper(context, ast), &[]));
        ast.method(
            &self.name,
            &self.parameters.to_viper_decl(context, ast),
            &self.targets.to_viper_decl(context, ast),
            &self.pres.to_viper(context, ast),
            &self.posts.to_viper(context, ast),
            body,
        )
    }
}
