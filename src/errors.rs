pub type Result<T, E = Error> = std::result::Result<T, E>;
pub(crate) type VerifyResult<T, E = VerificationError> = std::result::Result<T, E>;

#[derive(thiserror::Error, Debug, PartialEq)]
pub enum Error {
    /// An error occurred while parsing a method descriptor.
    #[error("Invalid method descriptor: {0}")]
    InvalidMethodDescriptor(String),
    /// An error occurred while looking for a method.
    #[error("No such method: {0}")]
    NoSuchMethod(String),
    /// An error occurred while verifying the method.
    #[error("Verification error: {0}")]
    VerificationError(#[from] VerificationError),
    /// An error occurred in [`ristretto_classfile`].
    #[error("{0}")]
    Ristretto(#[from] ristretto_classfile::Error),
}

#[derive(thiserror::Error, Debug, PartialEq)]
pub enum VerificationError {
    /// An error occurred while parsing a field type.
    #[error("Invalid field type: {0}")]
    InvalidFieldType(String),
    /// An error occurred while parsing a method descriptor.
    #[error("Invalid method descriptor: {0}")]
    InvalidMethodDescriptor(String),
    /// Illegal instruction encountered.
    #[error("Illegal instruction at #{0}: {1}")]
    IllegalInstruction(u16, ristretto_classfile::attributes::Instruction),
    /// Unsupported instruction encountered.
    #[error("Unsupported instruction at #{0}: {1}")]
    UnsupportedInstruction(u16, ristretto_classfile::attributes::Instruction),
    /// Recursion depth limit reached.
    #[error("Recursion depth limit reached after {0} iterations")]
    RecursionDepthLimitReached(u16),
    /// A block reference that used to exist is now gone. This is a bug!
    #[error("A block reference that used to exist is now gone. This is a bug!")]
    InvalidBlockReference,
    /// An error occurred while parsing a basic block during control flow analysis.
    #[error("This method appears to have no reachable exit point (invalid bytecode?)")]
    IllegalControlFlow(#[source] IllegalControlFlowReason),
    /// An type mismatch was detected while resolving a basic block.
    /// The string contains a description of the error as to what caused it.
    #[error("Type mismatch: {0}")]
    TypeMismatch(String),
    /// An error occurred in [`ristretto_classfile`].
    #[error("{0}")]
    Ristretto(#[from] ristretto_classfile::Error),
}

#[derive(thiserror::Error, Debug, PartialEq)]
pub enum IllegalControlFlowReason {
    /// Encountered a duplicate block while flattening the control flow graph.
    #[error("Encountered a duplicate block while flattening the control flow graph")]
    DuplicateBlocks,
    /// Encountered overlapping blocks with differing behavior. This is a bug!
    #[error("Encountered overlapping blocks with differing behavior. This is a bug!")]
    BehaviorMismatch,
    /// This method appears to have no reachable exit point (invalid bytecode?).
    /// The problematic block will have a [`pc_end`] of [`usize::MAX`].
    ///
    /// [`pc_end`]: crate::cfg::block::BasicBlock::pc_end
    #[error("This method appears to have no reachable exit point (invalid bytecode?)")]
    Unreachable,
}
