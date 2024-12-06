use std::{
    cell::{Ref, RefCell},
    ops::RangeInclusive,
    rc::{Rc, Weak},
};

use super::frame::{ControlFlowOutcome, StackFrame};
use crate::{IllegalControlFlowReason, Method, TryCatchBlock, VerificationError, VerifyResult};
use ristretto_classfile::{attributes::Instruction, ClassFile, ConstantPool};

/// A convenience macro for ending a basic block.
macro_rules! end_block {
    ($block:ident, $flags:expr, $range:expr) => {{
        let mut block = $block.borrow_mut();
        block.flags = $flags;
        block.range_pc = $range;
        Ok(Rc::downgrade(&$block))
    }};
}

/// A convenience macro for adding an edge to a basic block.
/// This is done because resolving a block requires an immutable borrow
/// (see exit_frame!), while pushing an edge requires a mutable borrow.
macro_rules! push_branch {
    ($block:ident, $($branch:tt)*) => {{
        let block = $($branch)*;
        $block.borrow_mut().edges.push(block);
    }};
}

/// A convenience macro for getting the exit frame of a basic block.
/// This immutably borrows the block and clones the exit frame.
macro_rules! exit_frame {
    ($block:ident) => {
        $block.borrow().exit_frame.clone()
    };
}

/// Validates that the given offset is within bounds of the given instructions.
/// If only a single offset is given, it will be read as an absolute offset.
/// If two offsets are given, they will be added up to form an absolute offset.
macro_rules! at_offset {
    ($context:ident($instruction:ident, $current:ident @ $offset:ident)) => {{
        // Validate the offset to make sure it's within bounds.
        if ($offset as usize) >= $context.instructions.len() {
            return Err(VerificationError::IllegalInstruction(
                $current,
                $instruction.clone(),
            ));
        }
        // Return the offset.
        $offset as u16
    }};
    ($context:ident($instruction:ident @ $current:ident + $offset:literal)) => {{
        // Validate the offset to make sure it's within bounds.
        let actual_offset = $current + $offset;
        if (actual_offset as usize) >= $context.instructions.len() {
            return Err(VerificationError::IllegalInstruction(
                $current,
                $instruction.clone(),
            ));
        }
        // Return the offset.
        actual_offset as u16
    }};
}

bitflags::bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct BasicBlockFlags: u8 {
        // This block contains an exit point (no edges).
        const EXIT_POINT = 1 << 0;
        // This block contains a decision point (2 edges).
        const DECISION_POINT = 1 << 1;
        // This block contains an unconditional jump (1 edge).
        const UNCONDITIONAL_JUMP = 1 << 2;
        // This block falls through to the next block (1 edge).
        const FALLTHROUGH = 1 << 3;
        // This block has no parent, and contains 0 or more edges.
        const EXCEPTION_HANDLER = 1 << 4;
    }
}

/// A context for resolving basic blocks.
pub(crate) struct BasicBlockContext<'a> {
    /// The class constant pool.
    pool: &'a mut ConstantPool,
    /// The list of instructions to process.
    instructions: &'a [Instruction],
    /// A list of all processed basic blocks.
    // This field is public for testing purposes.
    pub(super) blocks: &'a mut BasicBlockList,
    /// A list of exception handlers for this method (start_pc -> handler).
    exception_handlers: std::collections::HashMap<u16, Vec<&'a TryCatchBlock>>,
    /// An indicator that the next block is an exception handler.
    /// This is used internally in [`BasicBlock::resolve_branch`].
    next_is_exception_handler: bool,
}

impl<'a> BasicBlockContext<'a> {
    /// Creates a new [`BasicBlockContext`].
    pub fn new(
        pool: &'a mut ConstantPool,
        instructions: &'a [Instruction],
        blocks: &'a mut BasicBlockList,
        exception_handlers: &'a [TryCatchBlock],
    ) -> Self {
        Self {
            pool,
            instructions,
            blocks,
            exception_handlers: exception_handlers.iter().fold(
                std::collections::HashMap::new(),
                |mut map, handler| {
                    map.entry(handler.start_pc()).or_default().push(handler);
                    map
                },
            ),
            next_is_exception_handler: false,
        }
    }

    /// Returns a list of references to the exception handlers.
    /// This is necessary to prevent an immutable borrow on [`BasicBlockContext`].
    pub fn exception_handlers(&self) -> Vec<&'a TryCatchBlock> {
        self.exception_handlers
            .values()
            .flatten()
            .cloned()
            .collect()
    }

    /// Returns a strong reference to the [`BasicBlock`] that starts at the given program counter.
    /// If no such block exists, returns a [`VerificationError::InvalidBlockReference`].
    pub fn find_block(&self, pc: u16) -> VerifyResult<BasicBlockRef> {
        self.blocks
            .iter()
            .find(|block| block.borrow().pc_start() == pc)
            .cloned()
            .ok_or_else(|| VerificationError::InvalidBlockReference)
    }
}

/// A list of strong references to [`BasicBlocks`][BasicBlock].
pub type BasicBlockList = Vec<BasicBlockRef>;
/// A strong reference to a [`BasicBlock`].
pub type BasicBlockRef = Rc<RefCell<BasicBlock>>;
/// A weak reference to a [`BasicBlock`].
pub type BasicBlockWeakRef = Weak<RefCell<BasicBlock>>;

/// A basic block in the control flow graph.
#[derive(Clone)]
pub struct BasicBlock {
    // All of these fields are public for testing purposes.
    /// The flags of this basic block.
    pub(super) flags: BasicBlockFlags,
    // The range this basic block spans in the bytecode.
    pub(super) range_pc: RangeInclusive<u16>,
    /// The stack frame as it was when the basic block was entered.
    /// This can be the method entry point or from an edge (jump transition).
    pub(super) entry_frame: StackFrame,
    /// The stack frame as it was when the basic block was exited.
    /// This can be because the method returned or an edge (jump transition).
    pub(super) exit_frame: StackFrame,
    /// The edges of this basic block. These are jump transitions to another basic block.
    /// This is empty if, and only if the method contains no control flow branches.
    pub(super) edges: Vec<BasicBlockWeakRef>,
}

/// Contains the public API that is exposed to the user.
impl BasicBlock {
    /// Returns the flags of this basic block.
    pub fn flags(&self) -> BasicBlockFlags {
        self.flags
    }

    /// Returns the start PC of this basic block.
    pub fn pc_start(&self) -> u16 {
        *self.range_pc.start()
    }

    /// Returns the end PC of this basic block.
    pub fn pc_end(&self) -> u16 {
        *self.range_pc.end()
    }

    /// Returns the entry frame of this basic block.
    /// This is the stack frame as it was at the start
    /// of this basic block ([`BasicBlock::pc_start`]).
    pub fn entry_frame(&self) -> &StackFrame {
        &self.entry_frame
    }

    /// Returns the exit frame of this basic block.
    /// This is the stack frame as it was at the end
    /// of this basic block ([`BasicBlock::pc_end`]).
    pub fn exit_frame(&self) -> &StackFrame {
        &self.exit_frame
    }

    /// Returns an iterator over the edges of this basic block.
    /// Each edge is a reference to a [`BasicBlock`] that is reachable from this block.
    ///
    /// The result from the iterator is either a [`BlockEdgeRef`] or [`VerificationError::InvalidBlockReference`].
    /// The reference can be used to borrow the [`BasicBlock`] it points to.
    pub fn edges(&self) -> impl Iterator<Item = VerifyResult<BlockEdgeRef>> + '_ {
        self.edges.iter().map(|block| match Weak::upgrade(block) {
            Some(block) => Ok(BlockEdgeRef(block)),
            None => Err(VerificationError::InvalidBlockReference),
        })
    }
}

/// Contains the full implementation of [BasicBlock::resolve_branch].
impl BasicBlock {
    /// Recursively resolves the control flow graph of
    /// the given method via control flow analysis.
    pub(crate) fn resolve(
        context: &mut BasicBlockContext<'_>,
        entry_frame: StackFrame,
    ) -> VerifyResult<BasicBlockRef> {
        // Resolve the entry block.
        let entry_block = Self::resolve_branch(context, entry_frame, 0, 0)?;
        // Resolve the exception handlers.
        Self::resolve_exception_handlers(context)?;
        // Flatten the control flow graph.
        Self::flatten_graph(context)?;
        // This should never fail, but just to be sure.
        match Weak::upgrade(&entry_block) {
            Some(block) => Ok(block),
            None => Err(VerificationError::InvalidBlockReference),
        }
    }

    /// Resolves a distinct branch of the control flow graph.
    fn resolve_branch(
        context: &mut BasicBlockContext<'_>,
        entry_frame: StackFrame,
        nominal_offset: u16,
        recursion_depth: u16,
    ) -> VerifyResult<BasicBlockWeakRef> {
        // Make sure we don't end up in an infinite loop. This limit is just an arbitrary number.
        if recursion_depth > 100 {
            return Err(VerificationError::RecursionDepthLimitReached(
                recursion_depth - 1,
            ));
        }

        // Determine if this block is an exception handler.
        let is_exception_handler = context.next_is_exception_handler;
        context.next_is_exception_handler = false;

        // Find a block that exactly matches the given offset and entry frame.
        // This is to prevent us from getting stuck in an infinite loop.
        for block in context.blocks.iter() {
            // First, check if the block matches the given offset.
            let block_start = *block.borrow().range_pc.start();
            if block_start == nominal_offset {
                // Then, check if the block matches the given entry frame.
                if block.borrow().entry_frame == entry_frame {
                    // This is the same block, so return it.
                    return Ok(Rc::downgrade(block));
                }
                // We have multiple blocks pointing to the same offset,
                // but with different stack frames. This is a type mismatch!
                return Err(VerificationError::TypeMismatch(
                    StackFrame::describe_mismatch(
                        &block.borrow().entry_frame,
                        &entry_frame,
                        block_start,
                        &context.instructions[block_start as usize],
                    ),
                ));
            }
        }

        // Immediately create the block and mark it as visited.
        let block: Rc<RefCell<BasicBlock>> = Rc::new(RefCell::new(Self {
            // The flags may not be known yet at this point.
            flags: if is_exception_handler {
                BasicBlockFlags::EXCEPTION_HANDLER
            } else {
                BasicBlockFlags::empty()
            },
            // The end PC is not known yet at this point.
            range_pc: nominal_offset..=u16::MAX,
            entry_frame: entry_frame.clone(),
            exit_frame: entry_frame,
            edges: Vec::new(),
        }));
        // Mark the block as visited.
        context.blocks.push(Rc::clone(&block));

        let mut insn_offset = nominal_offset;
        while (insn_offset as usize) < context.instructions.len() {
            // Get the instruction at the current offset.
            let instruction = &context.instructions[insn_offset as usize];
            // Check if the current instruction is at a try-block boundary.
            if context.exception_handlers.contains_key(&insn_offset) {
                // If so, check if the current block contains any instructions.
                // All we care about is that we have a block at the try-block offset.
                // So if this is a new block or the beginning of the method, we're good.
                if insn_offset != nominal_offset {
                    // Begin a new basic block for the try-block.
                    // The catch block will need this later to recover the entry frame.
                    // Note though, this branch may exceed the range of the try-block.
                    push_branch!(
                        block,
                        Self::resolve_branch(
                            context,
                            exit_frame!(block),
                            insn_offset,
                            recursion_depth + 1,
                        )?
                    );
                    // End the current basic block as a fallthrough into the block above.
                    return end_block!(
                        block,
                        BasicBlockFlags::FALLTHROUGH,
                        nominal_offset..=insn_offset.saturating_sub(1)
                    );
                }
            }
            // Simulate the execution of the current instruction until we hit a decision point.
            let outcome = {
                // This needs to be in a separate scope to drop the mutable borrow.
                let mut block = block.borrow_mut();
                StackFrame::simulate_execution(
                    &mut block.exit_frame,
                    context.pool,
                    insn_offset,
                    instruction,
                )?
            };
            match outcome {
                /// Continue execution, do nothing.
                ControlFlowOutcome::Continue => {}
                /// Branch to the given offset. This ends the current basic block and begins
                /// a new basic block at the given offset and after the current instruction.
                ControlFlowOutcome::Branch(offset) => {
                    // Resolve the true branch at the given offset.
                    push_branch!(
                        block,
                        Self::resolve_branch(
                            context,
                            exit_frame!(block),
                            at_offset!(context(instruction, insn_offset @ offset)),
                            recursion_depth + 1,
                        )?
                    );
                    // Resolve the false branch at the current instruction.
                    push_branch!(
                        block,
                        Self::resolve_branch(
                            context,
                            exit_frame!(block),
                            at_offset!(context(instruction @ insn_offset + 1)),
                            recursion_depth + 1,
                        )?
                    );
                    // End the current basic block as a decision point.
                    return end_block!(
                        block,
                        BasicBlockFlags::DECISION_POINT,
                        nominal_offset..=insn_offset
                    );
                }
                /// Branch to any of the given offsets. This ends the current basic
                /// block and begins a new basic block at each of the given offsets.
                ControlFlowOutcome::Switch(offsets) => {
                    // Resolve each of the offsets.
                    for offset in offsets {
                        push_branch!(
                            block,
                            Self::resolve_branch(
                                context,
                                exit_frame!(block),
                                at_offset!(context(instruction, insn_offset @ offset)),
                                recursion_depth + 1,
                            )?
                        );
                    }
                    // End the current basic block as a decision point.
                    return end_block!(
                        block,
                        BasicBlockFlags::DECISION_POINT,
                        nominal_offset..=insn_offset
                    );
                }
                /// Jump to the given offset. This ends the current basic block
                /// and begins a new basic block at the given offset.
                ControlFlowOutcome::Jump(offset) => {
                    // Resolve the block at the given offset.
                    push_branch!(
                        block,
                        Self::resolve_branch(
                            context,
                            exit_frame!(block),
                            at_offset!(context(instruction, insn_offset @ offset)),
                            recursion_depth + 1,
                        )?
                    );
                    // End the current basic block as an unconditional jump.
                    return end_block!(
                        block,
                        BasicBlockFlags::UNCONDITIONAL_JUMP,
                        nominal_offset..=insn_offset
                    );
                }
                /// Throw an exception. This ends the current basic block.
                ControlFlowOutcome::Throw => {
                    // End the current basic block as an exit point.
                    return end_block!(
                        block,
                        BasicBlockFlags::EXIT_POINT,
                        nominal_offset..=insn_offset
                    );
                }
                /// Return from the current method. This ends the current basic block.
                ControlFlowOutcome::Return => {
                    // End the current basic block as an exit point.
                    return end_block!(
                        block,
                        BasicBlockFlags::EXIT_POINT,
                        nominal_offset..=insn_offset
                    );
                }
            }
            // Continue to the next instruction.
            insn_offset += 1;
        }

        // Only exit points allow us to end a basic block.
        // So if none was reached, return an error.
        Err(VerificationError::IllegalControlFlow(
            IllegalControlFlowReason::Unreachable,
        ))
    }

    /// Resolves all the exception handlers in the control flow graph.
    /// If this function returns `Ok(())`, the context will be mutated
    /// to contain the resolved exception handlers.
    fn resolve_exception_handlers(context: &mut BasicBlockContext<'_>) -> VerifyResult<()> {
        // If there are no exception handlers, there's nothing to resolve.
        if context.exception_handlers.is_empty() {
            return Ok(());
        }
        // Resolve the exception handlers.
        for handler in context.exception_handlers() {
            // Find the try-block from our earlier pass in resolve_branch().
            let try_block = context.find_block(handler.start_pc())?;
            // Initialize the stack frame for the exception handler. We use the
            // entry frame of the try-block to recover the available locals.
            let mut entry_frame = try_block.borrow().entry_frame().clone();
            entry_frame.reset_with_initial_stack(vec![handler.catch_type()]);
            // Resolve the exception handler (catch-block) with the entry frame.
            context.next_is_exception_handler = true;
            Self::resolve_branch(context, entry_frame, handler.handler_pc(), 0)?;
        }
        // Return success.
        Ok(())
    }

    /// Returns true if the flags and the amount of edges match.
    fn flags_and_edges_match(&self, other: &Self) -> bool {
        self.flags == other.flags && self.edges.len() == other.edges.len()
    }

    /// Sorts and flattens the control flow graph into a linear sequence of basic blocks.
    fn flatten_graph(context: &mut BasicBlockContext<'_>) -> VerifyResult<()> {
        // Fast path: if there's less than 3 blocks, return them as-is.
        // 2 or less blocks cannot overlap in any logical way.
        if context.blocks.len() < 3 {
            return Ok(());
        }
        // Sort the blocks by their start offset.
        context
            .blocks
            .sort_by_key(|block| *block.borrow().range_pc.start());
        // Keep track of which blocks we still have to process.
        let mut blocks: BasicBlockList = context.blocks.drain(..).collect();
        // Iterate through all the of the blocks.
        for current_block in blocks {
            // If this is the first block, we don't have a previous block yet.
            if let Some(previous_block) = context.blocks.last() {
                // Check if the current block overlaps with the previous block.
                let current_range = current_block.borrow().range_pc.clone();
                let previous_range = previous_block.borrow().range_pc.clone();
                let blocks_overlap = current_range.start() < previous_range.end()
                    && current_range.end() == previous_range.end();
                if blocks_overlap {
                    // If the current block starts before the previous block ends, it overlaps.
                    // Make sure both blocks have the same flags. If they don't, return an error.
                    let blocks_match = BasicBlock::flags_and_edges_match(
                        &current_block.borrow(),
                        &previous_block.borrow(),
                    );
                    if !blocks_match {
                        // We somehow have two blocks that overlap, but end up doing two entirely different things.
                        // This is definitely a bug in the stack simulation or control flow analysis.
                        return Err(VerificationError::IllegalControlFlow(
                            IllegalControlFlowReason::BehaviorMismatch,
                        ));
                    }
                    // We end the previous block at the current block's start position,
                    // and then add the current block as an edge to the previous block.
                    let mut block = previous_block.borrow_mut();
                    // The range is inclusive, so we need to subtract 1 from the end.
                    let range_start = current_range.start().saturating_sub(1);
                    block.range_pc = *previous_range.start()..=range_start;
                    block.edges = vec![Rc::downgrade(&current_block)];
                    // Make sure to retain the exception handler flag if it was set.
                    block.flags = (block.flags & BasicBlockFlags::EXCEPTION_HANDLER)
                        | BasicBlockFlags::FALLTHROUGH;
                    // ... add the current block to the processed list below.
                } else if current_range == previous_range {
                    // If both block ranges are equal, something has gone wrong earlier.
                    return Err(VerificationError::IllegalControlFlow(
                        IllegalControlFlowReason::DuplicateBlocks,
                    ));
                }
            }
            // Add the current block to the processed list.
            context.blocks.push(current_block);
        }
        // Return success.
        Ok(())
    }
}

// A custom implementation of PartialEq for BasicBlock.
// This is necessary to prevent infinite recursion (stack overflow)
// when comparing two BasicBlocks with edges that point to each other.
impl std::cmp::PartialEq for BasicBlock {
    fn eq(&self, other: &Self) -> bool {
        Self::shallow_eq(self, other)
            && self
                .edges
                .iter()
                .zip(other.edges.iter())
                .all(|(edge1, edge2)| Weak::ptr_eq(edge1, edge2))
    }
}

impl BasicBlock {
    /// Same as [BasicBlock::eq], but doesn't compare the edges.
    pub fn shallow_eq(&self, other: &Self) -> bool {
        self.flags == other.flags
            && self.range_pc == other.range_pc
            && self.entry_frame == other.entry_frame
            && self.exit_frame == other.exit_frame
            && self.edges.len() == other.edges.len()
    }
}

impl std::fmt::Debug for BasicBlock {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_with_visited(f, &mut std::collections::HashSet::new())
    }
}

impl BasicBlock {
    fn fmt_with_visited(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        visited: &mut std::collections::HashSet<*const Self>,
    ) -> std::fmt::Result {
        // Check if the current block was already visited.
        let self_ptr = self as *const Self;
        if visited.contains(&self_ptr) {
            return write!(
                f,
                "(cyclic reference to block {}..={})",
                self.range_pc.start(),
                self.range_pc.end()
            );
        }
        // If not, mark this block as visited.
        visited.insert(self_ptr);
        // Format the block and edges.
        f.debug_struct("BasicBlock")
            .field("flags", &self.flags)
            .field("range_pc", &self.range_pc)
            .field("entry_frame", &self.entry_frame)
            .field("exit_frame", &self.exit_frame)
            .field(
                "edges",
                &self
                    .edges
                    .iter()
                    .map(|edge| EdgeFormatter {
                        block: Weak::clone(edge),
                        visited,
                    })
                    .collect::<Vec<_>>(),
            )
            .finish()
    }
}

/// A not-so-nice workaround for printing basic blocks that contain cyclic references.
struct EdgeFormatter {
    block: BasicBlockWeakRef,
    // This is mutable aliasing. I know, that's bad. But as long
    // as we guarantee safety, this is not undefined behavior.
    visited: *mut std::collections::HashSet<*const BasicBlock>,
}

impl std::fmt::Debug for EdgeFormatter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.block.upgrade() {
            // Safety: We ensure exclusive access to the `visited` set across calls.
            Some(block) => unsafe { block.borrow().fmt_with_visited(f, &mut *self.visited) },
            None => write!(f, "<dead block>"),
        }
    }
}

/// A small wrapper around a [`BasicBlockRef`] to prevent it from being mutably borrowed.
pub struct BlockEdgeRef(BasicBlockRef);

impl BlockEdgeRef {
    /// Immutably borrows the [BasicBlock] referenced by this edge.
    ///
    /// The borrow lasts until the returned `Ref` exits scope. Multiple
    /// immutable borrows can be taken out at the same time.
    pub fn borrow(&self) -> Ref<'_, BasicBlock> {
        self.0.borrow()
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    macro_rules! test_blocks {
        ($(($flags:expr, $range:expr $(, [$($edges:literal),+])?)),+ $(,)?) => {{
            let edge_indices: Vec<&[usize]> = vec![$(&[$($($edges),+)?]),+];
            let mut blocks = vec![$(test_blocks!(@impl $flags, $range)),+];
            for (index, indices) in edge_indices.into_iter().enumerate() {
                let mut block = blocks[index].borrow_mut();
                for index in indices {
                    block.edges.push(Rc::downgrade(&blocks[*index]));
                }
            }
            blocks
        }};
        (@impl $flags:expr, $range:expr) => {
            Rc::new(RefCell::new(BasicBlock {
                flags: $flags,
                range_pc: $range,
                entry_frame: StackFrame::default(),
                exit_frame: StackFrame::default(),
                edges: vec![],
            }))
        };
    }

    macro_rules! blocks_eq {
        ($expected:expr, $actual:expr $(,)?) => {
            let (expected, actual) = ($expected, $actual);
            assert_eq!(
                expected.len(),
                actual.len(),
                "Blocks have different lengths"
            );
            let blocks = expected.into_iter().zip(actual.into_iter()).enumerate();
            for (index, (expected, actual)) in blocks {
                // Skip checking the frames, as it's too burdensome.
                let (expected, actual) = (expected.borrow(), actual.borrow());
                blocks_eq!(@assert index, expected.flags, actual.flags);
                blocks_eq!(@assert index, expected.range_pc, actual.range_pc);
                blocks_eq!(@assert index, expected.edges.len(), actual.edges.len());
            }
        };
        (@assert $index:ident, $a:expr, $b:expr) => {
            assert_eq!($a, $b, "Blocks at index {} are not equal!", $index);
        };
    }

    // Allow other modules to use these macros.
    pub(crate) use blocks_eq;
    pub(crate) use test_blocks;

    #[track_caller]
    fn test_flatten(input: &mut BasicBlockList, expected: &mut BasicBlockList) {
        let (mut pool1, mut pool2) = (ConstantPool::default(), ConstantPool::default());
        let mut expected = BasicBlockContext::new(&mut pool1, &[], expected, &[]);
        let mut actual = BasicBlockContext::new(&mut pool2, &[], input, &[]);
        BasicBlock::flatten_graph(&mut actual).unwrap();
        blocks_eq!(expected.blocks, actual.blocks);
    }

    #[test]
    fn test_flatten_simple() {
        // The input is pre-sorted for better readability.
        let mut input = test_blocks![
            /* 0 */ (BasicBlockFlags::DECISION_POINT, 0..=4, [4, 1]),
            /* 1 */ (BasicBlockFlags::DECISION_POINT, 5..=9, [3, 2]),
            /* 2 */ (BasicBlockFlags::EXIT_POINT, 10..=13),
            /* 3 */ (BasicBlockFlags::UNCONDITIONAL_JUMP, 14..=16, [5]),
            /* 4 */ (BasicBlockFlags::EXIT_POINT, 17..=20),
            /* 5 */ (BasicBlockFlags::EXIT_POINT, 19..=20),
        ];
        let mut expected = test_blocks![
            /* 0 */ (BasicBlockFlags::DECISION_POINT, 0..=4, [4, 1]),
            /* 1 */ (BasicBlockFlags::DECISION_POINT, 5..=9, [3, 2]),
            /* 2 */ (BasicBlockFlags::EXIT_POINT, 10..=13),
            /* 3 */ (BasicBlockFlags::UNCONDITIONAL_JUMP, 14..=16, [5]),
            /* 4 */ (BasicBlockFlags::FALLTHROUGH, 17..=18, [5]),
            /* 5 */ (BasicBlockFlags::EXIT_POINT, 19..=20),
        ];
        // Run the test.
        test_flatten(&mut input, &mut expected);
    }

    #[test]
    fn test_flatten_loop() {
        // The input is pre-sorted for better readability.
        let mut input = test_blocks![
            /* 0 */ (BasicBlockFlags::DECISION_POINT, 0..=5, [3, 2]),
            /* 1 */ (BasicBlockFlags::DECISION_POINT, 2..=5, [3, 2]),
            /* 2 */ (BasicBlockFlags::UNCONDITIONAL_JUMP, 6..=9, [1]),
            /* 3 */ (BasicBlockFlags::EXIT_POINT, 10..=13),
        ];
        let mut expected = test_blocks![
            /* 0 */ (BasicBlockFlags::FALLTHROUGH, 0..=1, [1]),
            /* 1 */ (BasicBlockFlags::DECISION_POINT, 2..=5, [3, 2]),
            /* 2 */ (BasicBlockFlags::UNCONDITIONAL_JUMP, 6..=9, [1]),
            /* 3 */ (BasicBlockFlags::EXIT_POINT, 10..=13),
        ];
        // Run the test.
        test_flatten(&mut input, &mut expected);
    }
}
