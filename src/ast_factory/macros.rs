#[macro_export]
macro_rules! jobject_wrapper {
    ($name:ident) => (
        pub struct $name<'a> { obj: JObject<'a> }
        impl<'a> $name<'a> {
            fn new(obj: JObject<'a>) -> Self {
                $name { obj }
            }
            pub fn to_jobject(&self) -> JObject {
                self.obj
            }
        }
    );
}

#[macro_export]
macro_rules! map_to_jobject {
    ($item:expr) => (
        $item.map(|x| x.to_jobject())
    );
}

#[macro_export]
macro_rules! map_to_jobjects {
    ($items:expr) => (
        map_to_jobject!($items.iter()).collect()
    );
}

#[macro_export]
macro_rules! build_ast_node {
    ($self:expr, $wrapper:path, $($java_class:ident)::+) => {
         {
            let obj = $self.jni.unwrap_result($($java_class)::+::with($self.env).new(
                $self.new_no_position().to_jobject(),
                $self.new_no_info(),
                $self.new_no_trafos(),
            ));
            $wrapper { obj }
        }
    };
    ($self:expr, $wrapper:path, $($java_class:ident)::+, $($args:expr),+) => {
         {
            let obj = $self.jni.unwrap_result($($java_class)::+::with($self.env).new(
                $($args),+ ,
                $self.new_no_position().to_jobject(),
                $self.new_no_info(),
                $self.new_no_trafos(),
            ));
            $wrapper { obj }
        }
    };
}
