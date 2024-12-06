use ristretto_classfile::attributes::{ExceptionTableEntry, VerificationType};

/// A wrapper around an [`ExceptionTableEntry`].
#[derive(Clone, Debug, PartialEq)]
pub struct TryCatchBlock {
    range_pc: std::ops::Range<u16>,
    handler_pc: u16,
    catch_type: u16,
}

impl TryCatchBlock {
    /// Creates a new [`TryCatchBlock`] from an [`ExceptionTableEntry`].
    pub(crate) fn from_entry(entry: &ExceptionTableEntry) -> Self {
        Self {
            range_pc: entry.range_pc.clone(),
            handler_pc: entry.handler_pc,
            catch_type: entry.catch_type,
        }
    }

    /// Returns the start PC of this try-catch block.
    pub fn start_pc(&self) -> u16 {
        self.range_pc.start
    }

    /// Returns the end PC (inclusive) of this try-catch block.
    pub fn end_pc(&self) -> u16 {
        self.range_pc.end - 1
    }

    /// Returns the handler PC of this try-catch block.
    pub fn handler_pc(&self) -> u16 {
        self.handler_pc
    }

    /// Returns `true` if the given instruction index is covered by this try-catch block.
    pub fn covers(&self, instruction_index: u16) -> bool {
        self.range_pc.contains(&instruction_index)
    }

    /// Returns the Throwable subclass type that is catched by this try-catch block.
    /// TODO: If catch_type is 0, this should return `Class("java/lang/Throwable")`.
    pub fn catch_type(&self) -> VerificationType {
        VerificationType::Object {
            cpool_index: self.catch_type,
        }
    }
}

impl From<ExceptionTableEntry> for TryCatchBlock {
    fn from(entry: ExceptionTableEntry) -> Self {
        Self::from_entry(&entry)
    }
}
