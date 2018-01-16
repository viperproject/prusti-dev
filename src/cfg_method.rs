use ast_factory::*;
use errors::Result as LocalResult;
use uuid::Uuid;

const LABEL_PREFIX: &'static str = "__viper";

pub struct CfgMethod<'a> {
    ast_factory: &'a AstFactory<'a>,
    uuid: Uuid,
    method_name: String,
    formal_args: Vec<LocalVarDecl<'a>>,
    formal_returns: Vec<LocalVarDecl<'a>>,
    local_vars: Vec<LocalVarDecl<'a>>,
    basic_blocks: Vec<CfgBlock<'a>>,
}

#[derive(Clone)]
struct CfgBlock<'a> {
    invs: Vec<Expr<'a>>,
    stmt: Stmt<'a>,
    successor: Successor<'a>,
}

#[derive(Clone)]
pub enum Successor<'a> {
    Unreachable(),
    Return(),
    Goto(CfgBlockIndex),
    GotoSwitch(Vec<(Expr<'a>, CfgBlockIndex)>),
    GotoIf(Expr<'a>, CfgBlockIndex, CfgBlockIndex),
}

#[derive(Clone, Copy)]
pub struct CfgBlockIndex {
    method_uuid: Uuid,
    block_index: usize,
}

impl<'a> CfgMethod<'a> {
    pub fn new(
        ast_factory: &'a AstFactory,
        method_name: String,
        formal_args: Vec<LocalVarDecl<'a>>,
        formal_returns: Vec<LocalVarDecl<'a>>,
        local_vars: Vec<LocalVarDecl<'a>>,
    ) -> Self {
        CfgMethod {
            ast_factory,
            uuid: Uuid::new_v4(),
            method_name: method_name,
            formal_args,
            formal_returns,
            local_vars,
            basic_blocks: vec![],
        }
    }

    pub fn add_block(&mut self, invs: Vec<Expr<'a>>, stmt: Stmt<'a>) -> CfgBlockIndex {
        let index = self.basic_blocks.len();
        self.basic_blocks.push(CfgBlock {
            invs,
            stmt,
            successor: Successor::Unreachable(),
        });
        CfgBlockIndex {
            method_uuid: self.uuid,
            block_index: index,
        }
    }

    pub fn set_successor(&mut self, index: CfgBlockIndex, successor: Successor<'a>) {
        assert_eq!(
            self.uuid, index.method_uuid,
            "The provided CfgBlockIndex doesn't belong to this CfgMethod"
        );
        self.basic_blocks[index.block_index].successor = successor;
    }

    pub fn to_ast(self) -> LocalResult<Method<'a>> {
        let mut blocks_ast: Vec<Stmt> = vec![];
        let mut labels: Vec<Stmt> = vec![];
        for (index, block) in self.basic_blocks.into_iter().enumerate() {
            blocks_ast.push(block_to_ast(
                self.ast_factory,
                &self.method_name,
                block,
                index,
            ));
            labels.push(
                self.ast_factory
                    .label(&index_to_label(&self.method_name, index), vec![]),
            );
        }
        blocks_ast.push(
            self.ast_factory
                .label(&return_label(&self.method_name), vec![]),
        );
        labels.push(
            self.ast_factory
                .label(&return_label(&self.method_name), vec![]),
        );

        let method_body = Some(self.ast_factory.seqn_with_labels(
            blocks_ast,
            self.local_vars,
            labels,
        ));

        let method = self.ast_factory.method(
            &self.method_name,
            self.formal_args,
            self.formal_returns,
            vec![],
            vec![],
            method_body,
        );

        Ok(method)
    }
}

fn index_to_label(method_name: &str, index: usize) -> String {
    format!("{}_{}_{}", LABEL_PREFIX, method_name, index)
}

fn return_label(method_name: &str) -> String {
    format!("{}_{}_return", LABEL_PREFIX, method_name)
}

fn successor_to_ast<'a>(
    ast: &'a AstFactory,
    method_name: &str,
    successor: Successor<'a>,
) -> Stmt<'a> {
    match successor {
        Successor::Unreachable() => ast.assert(ast.false_lit(), ast.no_position()),
        Successor::Return() => ast.goto(&return_label(method_name)),
        Successor::Goto(target) => ast.goto(&index_to_label(method_name, target.block_index)),
        Successor::GotoSwitch(ref successors) => {
            let skip = ast.seqn(vec![], vec![]);
            let mut stmts: Vec<Stmt> = vec![];
            for &(test, target) in successors {
                let goto = ast.goto(&index_to_label(method_name, target.block_index));
                let conditional_goto = ast.if_stmt(test, goto, skip);
                stmts.push(conditional_goto);
            }
            stmts.push(ast.assert(ast.false_lit(), ast.no_position()));
            ast.seqn(stmts, vec![])
        }
        Successor::GotoIf(test, then_target, else_target) => {
            let then_goto = ast.goto(&index_to_label(method_name, then_target.block_index));
            let else_goto = ast.goto(&index_to_label(method_name, else_target.block_index));
            ast.if_stmt(test, then_goto, else_goto)
        }
    }
}

fn block_to_ast<'a>(
    ast: &'a AstFactory,
    method_name: &str,
    block: CfgBlock<'a>,
    index: usize,
) -> Stmt<'a> {
    let label = index_to_label(method_name, index);
    ast.seqn(
        vec![
            ast.label(&label, block.invs),
            block.stmt,
            successor_to_ast(ast, method_name, block.successor),
        ],
        vec![],
    )
}
