#[macro_export]
macro_rules! jobject_wrapper {
    ($name:ident) => (
        pub struct $name<'a> { obj: JObject<'a> }

        impl<'a> $name<'a> {
            pub fn new(obj: JObject<'a>) -> Self {
                $name { obj }
            }
            pub fn to_jobject(&self) -> JObject {
                self.obj
            }
        }

        impl<'a> Clone for $name<'a> {
            fn clone(&self) -> Self { $name { obj: self.obj } }
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
macro_rules! map_to_jobject_pair {
    ($item:expr) => (
        $item.map(|x| (x.0.to_jobject(), x.1.to_jobject()))
    );
}

#[macro_export]
macro_rules! map_to_jobject_pairs {
    ($items:expr) => (
        map_to_jobject_pair!($items.iter()).collect()
    );
}

#[macro_export]
macro_rules! build_ast_node {
    ($self:expr, $wrapper:ident, $($java_class:ident)::+) => {
         {
            let obj = $self.jni.unwrap_result($($java_class)::+::with($self.env).new(
                $self.new_no_position().to_jobject(),
                $self.new_no_info(),
                $self.new_no_trafos(),
            ));
            $wrapper::new(obj)
        }
    };
    ($self:expr, $wrapper:ident, $($java_class:ident)::+, $($args:expr),+) => {
         {
            let obj = $self.jni.unwrap_result($($java_class)::+::with($self.env).new(
                $($args),+ ,
                $self.new_no_position().to_jobject(),
                $self.new_no_info(),
                $self.new_no_trafos(),
            ));
            $wrapper::new(obj)
        }
    };
}

#[macro_export]
macro_rules! get_ast_object {
    ($self:expr, $wrapper:ident, $($java_class:ident)::+) => {
         {
            let obj = $self.jni.unwrap_result($($java_class)::+::with($self.env).singleton());
            $wrapper::new(obj)
        }
    };
}
