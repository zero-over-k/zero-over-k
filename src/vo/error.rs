use std::num::ParseIntError;

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    PointLabelError(String),
    IntError(ParseIntError),
    UninitializedExpr,
    UninitializedLookupExpr,
    UninitializedLookupTableQuery,
}

impl Error {
    /// Convert an error in the underlying polynomial commitment scheme
    /// to a `Error`.
    pub fn from_parse_int_error(err: ParseIntError) -> Self {
        Error::IntError(err)
    }
}
