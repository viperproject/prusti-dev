// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#[macro_export]
macro_rules! jobject_wrapper {
    ($name:ident) => {
        #[derive(Copy, Clone)]
        pub struct $name<'a> {
            obj: JObject<'a>,
        }

        impl<'a> $name<'a> {
            pub(crate) fn new(obj: JObject<'a>) -> Self {
                $name { obj }
            }
            pub(crate) fn to_jobject(self) -> JObject<'a> {
                self.obj
            }
        }
    };
}

#[macro_export]
macro_rules! map_to_jobject {
    ($item:expr) => {
        $item.map(|x| x.to_jobject())
    };
}

#[macro_export]
macro_rules! map_to_jobjects {
    ($items:expr) => {
        map_to_jobject!($items.iter()).collect::<Vec<JObject>>()
    };
}

#[macro_export]
macro_rules! map_to_jobject_pair {
    ($item:expr) => {
        $item.map(|x| (x.0.to_jobject(), x.1.to_jobject()))
    };
}

#[macro_export]
macro_rules! map_to_jobject_pairs {
    ($items:expr) => {
        map_to_jobject_pair!($items.iter()).collect::<Vec<(JObject, JObject)>>()
    };
}

#[macro_export]
macro_rules! build_ast_node_with_pos {
    ($self:expr, $wrapper:ident, $($java_class:ident)::+, $($args:expr),+) => {
         {
            let obj = $self.jni.unwrap_result(
                $self.env.with_local_frame(16, move || {
                    $($java_class)::+::with($self.env).new(
                        $($args),+ ,
                        $self.no_info(),
                        $self.no_trafos(),
                    )
                })
            );
            $wrapper::new(obj)
        }
    };
}

#[macro_export]
macro_rules! build_ast_node {
    ($self:expr, $wrapper:ident, $($java_class:ident)::+) => {
         build_ast_node_with_pos!(
            $self,
            $wrapper,
            $($java_class)::+,
            $self.no_position().to_jobject()
         )
    };
    ($self:expr, $wrapper:ident, $($java_class:ident)::+, $($args:expr),+) => {
         build_ast_node_with_pos!(
            $self,
            $wrapper,
            $($java_class)::+,
            $($args),+ ,
            $self.no_position().to_jobject()
         )
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

#[macro_export]
macro_rules! generate_conversion_from_to {
    ($from:ident, $to:ident) => {
        impl<'a> From<$from<'a>> for $to<'a> {
            fn from(other: $from<'a>) -> Self {
                $to::new(other.to_jobject())
            }
        }
    };
}
