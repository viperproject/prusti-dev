use super::{graph::Row, to_text::ToText};

pub(super) trait ToRow {
    fn to_row(self) -> Row;
}

impl<S: ToText> ToRow for Vec<S> {
    fn to_row(self) -> Row {
        Row::Seq(self.into_iter().map(|column| column.to_text()).collect())
    }
}
