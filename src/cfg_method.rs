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
    stmt: Stmt<'a>,
    successor: Successor<'a>
}

#[derive(Clone)]
pub enum Successor<'a> {
    Unreachable(),
    Return(),
    Goto(CfgBlockIndex),
    Switch(Vec<(Expr<'a>, CfgBlockIndex)>),
    If(Expr<'a>, CfgBlockIndex, CfgBlockIndex)
}

#[derive(Clone, Copy)]
pub struct CfgBlockIndex {
    method_uuid: Uuid,
    block_index: usize
}

impl<'a> CfgMethod<'a> {
    pub fn new(ast_factory: &'a AstFactory, method_name: String, formal_args: Vec<LocalVarDecl<'a>>, formal_returns: Vec<LocalVarDecl<'a>>, local_vars: Vec<LocalVarDecl<'a>>) -> Self
    {
        CfgMethod {
            ast_factory,
            uuid: Uuid::new_v4(),
            method_name: method_name,
            formal_args,
            formal_returns,
            local_vars,
            basic_blocks: vec![]
        }
    }

    pub fn add_block(&mut self, stmt: Stmt<'a>) -> CfgBlockIndex {
        let index = self.basic_blocks.len();
        self.basic_blocks.push(
            CfgBlock {
                stmt,
                successor: Successor::Unreachable()
            }
        );
        CfgBlockIndex{
            method_uuid: self.uuid,
            block_index: index
        }
    }

    pub fn set_successor(&mut self, index: CfgBlockIndex, successor: Successor<'a>) {
        assert_eq!(self.uuid, index.method_uuid, "The provided CfgBlockIndex doesn't belong to this CfgMethod");
        self.basic_blocks[index.block_index].successor = successor;
    }

    fn index_to_label(&self, index: usize) -> String {
        format!("{}_{}_{}", LABEL_PREFIX, self.method_name, index)
    }

    fn return_label(&self) -> String {
        format!("{}_{}_return", LABEL_PREFIX, self.method_name)
    }

    fn successor_to_ast(&self, successor: &Successor) -> Stmt {
        let ast = self.ast_factory;
        match successor {
            &Successor::Unreachable() => ast.assert(ast.false_lit(), ast.no_position()),
            &Successor::Return() => ast.goto(&self.return_label()),
            &Successor::Goto(target) => ast.goto(&self.index_to_label(target.block_index)),
            &Successor::Switch(ref successors) => {
                let skip = ast.seqn(vec![], vec![]);
                let mut stmts: Vec<Stmt> = vec![];
                for &(test, target) in successors {
                    let goto = ast.goto(&self.index_to_label(target.block_index));
                    let conditional_goto = ast.if_stmt(test, goto, skip);
                    stmts.push(conditional_goto);
                }
                stmts.push(ast.assert(ast.false_lit(), ast.no_position()));
                ast.seqn(stmts, vec![])
            },
            &Successor::If(test, then_target, else_target) => {
                let then_goto = ast.goto(&self.index_to_label(then_target.block_index));
                let else_goto = ast.goto(&self.index_to_label(else_target.block_index));
                ast.if_stmt(test, then_goto, else_goto)
            }
        }
    }

    fn block_to_ast(&self, index: usize) -> Stmt {
        let block = &self.basic_blocks[index];
        let ast = self.ast_factory;
        let label = self.index_to_label(index);
        ast.seqn(
            vec![
                ast.label(&label, vec![]), // TODO: we probably need label invariants...
                block.stmt,
                self.successor_to_ast(&block.successor)
            ],
            vec![]
        )
    }

    pub fn to_ast(self) -> LocalResult<Method<'a>> {
        let num_basic_blocks = self.basic_blocks.len();
        let method_body = {
            let mut blocks_ast: Vec<Stmt> = (0..num_basic_blocks).map(|x| self.block_to_ast(x)).collect();
            blocks_ast.push(self.ast_factory.label(&self.return_label(), vec![]));
            let mut labels: Vec<Stmt> = (0..num_basic_blocks).map(|x| self.ast_factory.label(&self.index_to_label(x), vec![])).collect();
            labels.push(self.ast_factory.label(&self.return_label(), vec![]));
            Some(
                self.ast_factory.seqn_with_labels(
                    blocks_ast,
                    self.local_vars.clone(),
                    labels
                )
            )
        };

        let method = self.ast_factory.method(
            &self.method_name,
            self.formal_args,
            self.formal_returns,
            vec![],
            vec![],
            method_body
        );

        Ok(method)
    }
}
