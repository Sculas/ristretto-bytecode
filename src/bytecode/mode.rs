pub enum CompilationMode {
    /// Computes nothing and leaves the stack map table as is.
    /// This is safe to use as long as you don't add or remove any instructions.
    ComputeNothing,
    /// Recomputes the stack map table, stack max size, and local max size.
    /// This is an expensive operation, but is required if instructions are added or removed.
    ComputeAll,
}
