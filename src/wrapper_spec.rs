pub struct ClassWrapperSpec {
    pub full_class_name: String,
    pub items: Vec<ItemWrapperSpec>,
}

pub enum ItemWrapperSpec {
    ScalaObjectGetter(),
    Constructor {
        signature: Option<String>,
        suffix: Option<String>,
    },
    Method {
        name: String,
        signature: Option<String>,
        suffix: Option<String>,
    },
}

#[macro_export]
macro_rules! java_class {
    ($full_class_name:expr) => (
        ClassWrapperSpec{
            full_class_name: $full_class_name.into(),
            items: vec![]
        }
    );
    ($full_class_name:expr, $items:expr) => (
        ClassWrapperSpec{
            full_class_name: $full_class_name.into(),
            items: $items
        }
    );
}

#[macro_export]
macro_rules! object_getter {
    () => (
        ItemWrapperSpec::ScalaObjectGetter()
    );
}

#[macro_export]
macro_rules! constructor {
    () => (
        ItemWrapperSpec::Constructor { signature: None, suffix: None }
    );
    ($signature:expr) => (
        ItemWrapperSpec::Constructor { signature: Some($signature.into()), suffix: None }
    );
    ($signature:expr, $suffix:expr) => (
        ItemWrapperSpec::Constructor { signature: $signature.into(), suffix: Some($suffix.into()) }
    );
}

#[macro_export]
macro_rules! method {
    ($name:expr) => (
        ItemWrapperSpec::Method {
            name: $name.into(),
            signature: None,
            suffix: None
        }
    );
    ($name:expr, $signature:expr) => (
        ItemWrapperSpec::Method {
            name: $name.into(),
            signature: Some($signature.into()),
            suffix: None
        }
    );
    ($name:expr, $signature:expr, $suffix:expr) => (
        ItemWrapperSpec::Method {
            name: $name.into(),
            signature: Some($signature.into()),
            suffix: Some($suffix.into())
        }
    );
}
