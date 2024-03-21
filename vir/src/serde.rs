use serde::{
    ser::{Serialize, Serializer},
    de::{Deserialize, Deserializer},
};

pub mod serde_slice {
    use super::*;

    pub fn serialize<'vir, S, T>(data: &'vir [&'vir T], ser: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
        T: Serialize,
    {
        // TODO: unnecessary copy
        let vec = data.iter().collect::<Vec<_>>();
        vec.serialize(ser)
    }

    pub fn deserialize<'vir, D, T>(deser: D) -> Result<&'vir [&'vir T], D::Error>
    where
        D: Deserializer<'vir>,
        T: Deserialize<'vir>,
    {
        crate::with_vcx(|vcx| {
            let vec = Vec::<T>::deserialize(deser)?
                .into_iter()
                // TODO: unnecessary copy
                .map(|el| vcx.alloc(el))
                .collect::<Vec<_>>();
            Ok(vcx.alloc_slice(&vec))
        })
    }
}

pub mod serde_ref {
    use super::*;

    pub fn serialize<'vir, S, T>(data: &'vir T, ser: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
        T: Serialize,
    {
        data.serialize(ser)
    }

    pub fn deserialize<'vir, D, T>(deser: D) -> Result<&'vir T, D::Error>
    where
        D: Deserializer<'vir>,
        T: Deserialize<'vir>,
    {
        crate::with_vcx(|vcx| {
            let el = T::deserialize(deser)?;
            Ok(vcx.alloc(el))
        })
    }
}

pub mod serde_str {
    use super::*;

    pub fn serialize<'vir, S>(data: &'vir str, ser: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        data.serialize(ser)
    }

    pub fn deserialize<'vir, D>(deser: D) -> Result<&'vir str, D::Error>
    where
        D: Deserializer<'vir>,
    {
        crate::with_vcx(|vcx| {
            let el = String::deserialize(deser)?;
            Ok(vcx.alloc_str(&el))
        })
    }
}
