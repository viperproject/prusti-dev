use super::{
    super::super::ast::{
        expression::Expression,
        ty,
        ty::{visitors::TypeWalker, ConstGenericArgument},
    },
    WithConstArguments,
};

fn collect_const_arguments(ty: &ty::Type, arguments: &mut Vec<Expression>) {
    struct Collector<'a> {
        arguments: &'a mut Vec<Expression>,
    }
    impl<'a> TypeWalker for Collector<'a> {
        fn walk_const_generic_argument(&mut self, argument: &ConstGenericArgument) {
            self.arguments
                .push((**argument.value.as_ref().unwrap()).clone());
        }
    }
    let mut collector = Collector { arguments };
    collector.walk_type(ty);
}

impl WithConstArguments for ty::Type {
    fn get_const_arguments(&self) -> Vec<Expression> {
        let mut arguments = Vec::new();
        collect_const_arguments(self, &mut arguments);
        arguments
    }
}
