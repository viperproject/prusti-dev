use super::IntoSnapshot;
use crate::encoder::{errors::SpannedEncodingResult, middle::core_proof::lowerer::Lowerer};

impl<T: IntoSnapshot> IntoSnapshot for Vec<T> {
    type Target = Vec<T::Target>;
    fn create_snapshot<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        let mut vec = Vec::new();
        for element in self {
            vec.push(element.create_snapshot(lowerer)?);
        }
        Ok(vec)
    }
}
