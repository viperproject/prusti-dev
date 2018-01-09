use viper_sys::wrappers::viper::silver::ast;
use ast_factory::AstFactory;
use ast_factory::structs::Expr;
use ast_factory::structs::Stmt;
use ast_factory::structs::Program;
use ast_factory::structs::Domain;
use ast_factory::structs::Field;
use ast_factory::structs::Function;
use ast_factory::structs::Predicate;
use ast_factory::structs::Method;
use ast_factory::structs::Type;
use ast_factory::structs::LocalVarDecl;
use ast_factory::structs::DomainFunc;
use ast_factory::structs::DomainAxiom;

impl<'a> AstFactory<'a> {
    pub fn program(
        &self,
        domains: Vec<Domain>,
        fields: Vec<Field>,
        functions: Vec<Function>,
        predicates: Vec<Predicate>,
        methods: Vec<Method>,
    ) -> Program<'a> {
        build_ast_node!(
            self,
            Program,
            ast::Program,
            self.jni.new_seq(map_to_jobjects!(domains)),
            self.jni.new_seq(map_to_jobjects!(fields)),
            self.jni.new_seq(map_to_jobjects!(functions)),
            self.jni.new_seq(map_to_jobjects!(predicates)),
            self.jni.new_seq(map_to_jobjects!(methods))
        )
    }

    pub fn field(&self, name: &str, typ: Type) -> Field<'a> {
        build_ast_node!(
            self,
            Field,
            ast::Field,
            self.jni.new_string(name),
            typ.to_jobject()
        )
    }

    pub fn local_var_decl(&self, name: &str, typ: Type) -> LocalVarDecl<'a> {
        build_ast_node!(
            self,
            LocalVarDecl,
            ast::LocalVarDecl,
            self.jni.new_string(name),
            typ.to_jobject()
        )
    }

    pub fn predicate(
        &self,
        name: &str,
        formal_args: Vec<LocalVarDecl>,
        body: Option<Expr>,
    ) -> Predicate<'a> {
        build_ast_node!(
            self,
            Predicate,
            ast::Predicate,
            self.jni.new_string(name),
            self.jni.new_seq(map_to_jobjects!(formal_args)),
            match body {
                None => self.jni.new_option(None),
                Some(x) => self.jni.new_option(Some(x.to_jobject())),
            }
        )
    }

    pub fn function(
        &self,
        name: &str,
        formal_args: Vec<LocalVarDecl>,
        typ: Type,
        pres: Vec<Expr>,
        posts: Vec<Expr>,
        body: Option<Expr>,
    ) -> Function<'a> {
        build_ast_node!(
            self,
            Function,
            ast::Function,
            self.jni.new_string(name),
            self.jni.new_seq(map_to_jobjects!(formal_args)),
            typ.to_jobject(),
            self.jni.new_seq(map_to_jobjects!(pres)),
            self.jni.new_seq(map_to_jobjects!(posts)),
            self.jni.new_option(None), // decs: Option[DecClause]
            match body {
                None => self.jni.new_option(None),
                Some(x) => self.jni.new_option(Some(x.to_jobject())),
            }
        )
    }

    pub fn method(
        &self,
        name: &str,
        formal_args: Vec<LocalVarDecl>,
        formal_returns: Vec<LocalVarDecl>,
        pres: Vec<Expr>,
        posts: Vec<Expr>,
        body: Option<Vec<Stmt>>,
    ) -> Method<'a> {
        build_ast_node!(
            self,
            Method,
            ast::Method,
            self.jni.new_string(name),
            self.jni.new_seq(map_to_jobjects!(formal_args)),
            self.jni.new_seq(map_to_jobjects!(formal_returns)),
            self.jni.new_seq(map_to_jobjects!(pres)),
            self.jni.new_seq(map_to_jobjects!(posts)),
            match body {
                None => self.jni.new_option(None),
                Some(x) => self.jni.new_option(Some(self.seqn(x).to_jobject())),
            }
        )
    }

    pub fn domain(
        &self,
        name: &str,
        functions: Vec<DomainFunc>,
        axioms: Vec<DomainAxiom>,
        type_vars: Vec<Type>,
    ) -> Domain<'a> {
        build_ast_node!(
            self,
            Domain,
            ast::Domain,
            self.jni.new_string(name),
            self.jni.new_seq(map_to_jobjects!(functions)),
            self.jni.new_seq(map_to_jobjects!(axioms)),
            self.jni.new_seq(map_to_jobjects!(type_vars))
        )
    }

    pub fn domain_func(
        &self,
        name: &str,
        formal_args: Vec<LocalVarDecl>,
        typ: Type,
        unique: bool,
        domain_name: &str,
    ) -> DomainFunc<'a> {
        let obj = self.jni.unwrap_result(ast::DomainFunc::with(self.env).new(
            self.jni.new_string(name),
            self.jni.new_seq(map_to_jobjects!(formal_args)),
            typ.to_jobject(),
            unique as u8, // TODO: perform the `as u8` conversion in the `jni-gen` crate
            self.no_position().to_jobject(),
            self.no_info(),
            self.jni.new_string(domain_name),
            self.no_trafos(),
        ));
        DomainFunc::new(obj)
    }

    pub fn domain_axiom(&self, name: &str, expr: Expr, domain_name: &str) -> DomainAxiom<'a> {
        let obj = self.jni.unwrap_result(ast::DomainAxiom::with(self.env).new(
            self.jni.new_string(name),
            expr.to_jobject(),
            self.no_position().to_jobject(),
            self.no_info(),
            self.jni.new_string(domain_name),
            self.no_trafos(),
        ));
        DomainAxiom::new(obj)
    }
}
