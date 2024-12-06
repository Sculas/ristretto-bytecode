use std::{
    cell::{Ref, RefCell},
    ops::RangeInclusive,
    rc::{Rc, Weak},
};

use crate::{Method, VerifyResult};
use block::*;
use frame::*;
use ristretto_classfile::ClassFile;

pub(crate) mod block;
pub(crate) mod frame;
mod utils;

/// A control flow graph (CFG) constructed from Java bytecode.
#[derive(Debug, Clone)]
pub struct ControlFlowGraph {
    /// A vector of all basic blocks in the CFG.
    blocks: BasicBlockList,
    /// A strong reference to the entry block in the CFG.
    entry_block: Rc<RefCell<BasicBlock>>,
}

impl ControlFlowGraph {
    /// Constructs a new control flow graph from the given class and method.
    pub fn construct(class: &mut ClassFile, method: &Method) -> VerifyResult<Self> {
        // Initialize the entry frame for the method entrypoint basic block.
        // This frame should not be written to the table, as it's calculated by the JVM itself.
        let entry_frame = StackFrame::create_entry(class, method)?;
        // Initialize the basic block for the entrypoint. This function will run
        // recursively until all blocks are resolved and the CFG is complete.
        let mut blocks = Vec::new();
        let entry_block = BasicBlock::resolve(
            &mut BasicBlockContext::new(
                &mut class.constant_pool,
                &method.instructions,
                &mut blocks,
                &method.try_catch_blocks,
            ),
            entry_frame,
        )?;
        // Return the constructed CFG.
        Ok(Self {
            blocks,
            entry_block,
        })
    }

    /// Returns the entry block of the control flow graph.
    pub fn entrypoint(&self) -> Ref<'_, BasicBlock> {
        self.entry_block.borrow()
    }

    /// Transforms the control flow graph into a [`StackMapTable`][StackMapTable].
    ///
    /// [StackMapTable]: ristretto_classfile::attributes::Attribute::StackMapTable
    pub fn into_table(self) {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{bytecode::cfg::block::tests::*, *};

    macro_rules! test_method {
        ($file:literal, $descriptor:expr) => {{
            use std::io::Cursor;
            let mut bytes = Cursor::new(include_bytes!(concat!("../../../tests/", $file)).to_vec());
            let class = ristretto_classfile::ClassFile::from_bytes(&mut bytes).unwrap();
            let method = class.method($descriptor).unwrap();
            (class, method)
        }};
    }

    #[track_caller]
    fn test_construct(class: &mut ClassFile, method: &Method) -> ControlFlowGraph {
        match ControlFlowGraph::construct(class, &method) {
            Ok(cfg) => cfg,
            Err(e) => {
                panic!("Failed to construct CFG: {e}\n\nMethod: {method}\n\nClass: {class}");
            }
        }
    }

    /// Tests a couple of simple instructions inside of the `SimpleTest.java` class.
    #[test]
    fn test_simple() {
        let (mut class, method) = test_method!("SimpleTest.class", ("example", "(I)I"));
        let cfg = test_construct(&mut class, &method);

        let mut expected = test_blocks![
            /* 0 */ (BasicBlockFlags::DECISION_POINT, 0..=4, [4, 1]),
            /* 1 */ (BasicBlockFlags::DECISION_POINT, 5..=9, [3, 2]),
            /* 2 */ (BasicBlockFlags::EXIT_POINT, 10..=13),
            /* 3 */ (BasicBlockFlags::UNCONDITIONAL_JUMP, 14..=16, [5]),
            /* 4 */ (BasicBlockFlags::FALLTHROUGH, 17..=18, [5]),
            /* 5 */ (BasicBlockFlags::EXIT_POINT, 19..=20),
        ];

        blocks_eq!(expected, cfg.blocks);
    }

    /// Tests almost all Java instructions inside of the `ComplexTest.java` class.
    #[test]
    fn test_complex() {
        let (mut class, method) = test_method!("ComplexTest.class", ("example", "()V"));
        let _cfg = test_construct(&mut class, &method);
        // TODO: Check if the control flow graph is correct.
    }

    /// Specifically tests if exceptions are handled correctly from the `Exceptions.java` class.
    #[test]
    fn test_exceptions() {
        let (mut class, method) = test_method!("Exceptions.class", ("example", "()V"));
        let _cfg = test_construct(&mut class, &method);
        // TODO: Check if the control flow graph is correct.
    }
}
