use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError {
    /// Byte offset in the source string.
    pub offset: usize,
    pub message: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "parse error at byte {}: {}", self.offset, self.message)
    }
}

impl std::error::Error for ParseError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolveError {
    pub name: String,
}

impl fmt::Display for ResolveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "unbound name: {}", self.name)
    }
}

impl std::error::Error for ResolveError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FrontendError {
    Parse(ParseError),
    Resolve(ResolveError),
}

impl fmt::Display for FrontendError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Parse(error) => error.fmt(f),
            Self::Resolve(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for FrontendError {}

impl From<ParseError> for FrontendError {
    fn from(error: ParseError) -> Self {
        Self::Parse(error)
    }
}

impl From<ResolveError> for FrontendError {
    fn from(error: ResolveError) -> Self {
        Self::Resolve(error)
    }
}
