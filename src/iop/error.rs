#[derive(Debug, PartialEq)]
pub enum Error {
    MissingConcreteEval,
    WtnsQueryIndexOutOfBounds(usize),
    InstanceQueryIndexOutOfBounds(usize),
    ExtendedEvalsMissing,
    ZeroQuotientPoly,
}
