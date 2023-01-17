#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    PointLabelError(String),
    UninitializedExpr,
    UninitializedLookupExpr,
    UninitializedLookupTableQuery,
}
