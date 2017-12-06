// Implements a public getter for a given Scala object
macro_rules! pub_scala_object_getter {
    ($fn_name: ident, $object_full_path: expr) => {
        pub fn $fn_name<'a>(env: &'a JNIEnv) -> Result<JObject<'a>, Error> {
            env.get_static_field(
                concat!($object_full_path, "$"),
                "MODULE$",
                concat!("L", $object_full_path, "$;"),
            ).and_then(|x| x.l())
        }
    };
}
