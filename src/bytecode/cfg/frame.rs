use std::borrow::Cow;

use super::utils::*;
use crate::{Method, VerificationError, VerifyResult};
use ristretto_classfile::{
    attributes::{ArrayType, Instruction, VerificationType},
    ClassFile, Constant, ConstantPool, MethodAccessFlags,
};

// TODO: Improve documentation.

macro_rules! error {
    ($instruction_index:ident, $instruction:ident) => {
        Err(error!([noerr] $instruction_index, $instruction))
    };
    ([noerr] $instruction_index:ident, $instruction:ident) => {
        VerificationError::IllegalInstruction($instruction_index, $instruction.clone())
    };
}

macro_rules! push_continue {
    ($frame:expr, [$($kind:ident),+]) => {{
        $frame.stack.extend_from_slice(&[$(VerificationType::$kind),+]);
        ControlFlowOutcome::Continue
    }};
    ($frame:expr, $kind:ident) => {{
        $frame.stack.push(VerificationType::$kind);
        ControlFlowOutcome::Continue
    }};
    ($frame:ident object $index:ident) => {{
        $frame.stack.push(VerificationType::Object { cpool_index: $index });
        ControlFlowOutcome::Continue
    }};
    ($frame:ident object $expr:expr) => {{
        $frame.stack.push($expr);
        ControlFlowOutcome::Continue
    }};
}

macro_rules! try_pop_stack {
    ($frame:expr, $instruction_index:ident, $instruction:ident $(, $kind:pat)?) => {{
        match $frame.stack.pop() {
            Some(value $(@ $kind)?) => Ok(value),
            _ => error!($instruction_index, $instruction),
        }
    }};
}

macro_rules! try_pop_stack_n {
    ($frame:expr, $instruction_index:ident, $instruction:ident, $amount:literal) => {{
        // Make sure the stack has at least N elements.
        let stack_len = $frame.stack.len();
        if stack_len < $amount {
            error!($instruction_index, $instruction)
        } else {
            // Drain the stack and collect the values into an array.
            let mut v = $frame.stack.drain((stack_len - $amount)..stack_len);
            // It's safe to unwrap this, since we checked the length above.
            Ok(std::array::from_fn::<_, $amount, _>(|_| v.next().unwrap()))
        }
    }};
    ($frame:expr, $instruction_index:ident, $instruction:ident, $amount:literal [noreturn]) => {{
        // Make sure the stack has at least N elements.
        let stack_len = $frame.stack.len();
        if stack_len < $amount {
            error!($instruction_index, $instruction)
        } else {
            // Immediately drop the values.
            $frame.stack.drain((stack_len - $amount)..stack_len);
            Ok(())
        }
    }};
}

macro_rules! try_pop_stack_eq {
    ($frame:expr, $instruction_index:ident, $instruction:ident, $type:expr) => {{
        match $frame.stack.pop() {
            Some(value) if value == $type => Ok(value),
            _ => error!($instruction_index, $instruction),
        }
    }};
}

macro_rules! try_pop_stack_checked {
    ($frame:expr, $instruction_index:ident, $instruction:ident, $type:expr) => {{
        // Wide types are padded, so pop the padding off the stack first.
        if is_wide_type(&$type) {
            // Verify that the wide type is actually padded.
            try_pop_stack!(
                $frame,
                $instruction_index,
                $instruction,
                VerificationType::Top
            )?;
        }
        match $frame.stack.pop() {
            Some(value) if value == $type => Ok(value),
            _ => error!($instruction_index, $instruction),
        }
    }};
    ($frame:expr, $instruction_index:ident, $instruction:ident) => {{
        // Pop the first value off the stack.
        let mut value = try_pop_stack!($frame, $instruction_index, $instruction)?;
        // If it's a wide type, pop the actual value off the stack.
        if value == VerificationType::Top {
            value = try_pop_stack!(
                $frame,
                $instruction_index,
                $instruction,
                VerificationType::Double | VerificationType::Long
            )?;
        }
        // Return the value.
        value
    }};
}

macro_rules! try_get_local {
    ($frame:expr, $instruction_index:ident, $instruction:ident, $index:expr, $pattern:pat) => {{
        match $frame.locals.get($index as usize) {
            Some(local @ $pattern) => Ok(local),
            _ => error!($instruction_index, $instruction),
        }
    }};
}

macro_rules! try_get_local_eq {
    ($frame:expr, $instruction_index:ident, $instruction:ident, $index:expr, $type:expr) => {{
        match $frame.locals.get($index as usize) {
            Some(local) if local == $type => Ok(local),
            _ => error!($instruction_index, $instruction),
        }
    }};
}

macro_rules! try_set_local {
    ($frame:expr, $instruction_index:ident, $instruction:ident, $index:expr, $value:expr) => {{
        match $frame.locals.get($index as usize) {
            // Check if a local variable at the given index already exists.
            Some(local) => {
                // Set the local variable to the given value.
                $frame.locals[$index as usize] = $value;
                Ok(())
            }
            // Increase the locals max size to accommodate the new local variable.
            None => {
                // Check if there would be gaps in the locals, which is not allowed.
                if $index as usize >= $frame.locals.len() {
                    // There are no gaps, so set the local variable.
                    // We can use `push` here because we checked the index above.
                    $frame.locals.push($value);
                    Ok(())
                } else {
                    // There would be gaps, so return an error.
                    error!($instruction_index, $instruction)
                }
            }
        }
    }};
}

macro_rules! short_index {
    ($local_index:ident, $instruction_index:ident, $instruction:ident) => {
        TryInto::<u16>::try_into($local_index).map_err(|_| error!([noerr] $instruction_index, $instruction))?
    };
}

#[derive(Debug, Default, Clone, PartialEq)]
pub enum ControlFlowOutcome {
    /// Execution continues as normal.
    #[default]
    Continue,
    /// Execution branches to the given offset or continues to the next instruction.
    Branch(u16),
    /// Execution branches to any of the given offsets.
    Switch(Vec<u16>),
    /// Execution jumps to the given offset.
    Jump(u16),
    /// Execution halts, the stack frame is reset, and the exception handler is ran.
    Throw,
    /// Execution ends and returns from the current method.
    Return,
}

/// A single stack frame used during control flow analysis to determine the stack map table.
#[derive(Debug, Default, Clone, PartialEq)]
pub struct StackFrame {
    /// A list of local variables used in this frame.
    locals: Vec<VerificationType>,
    /// A list of stack values on the operand stack.
    stack: Vec<VerificationType>,
}

impl StackFrame {
    /// Returns the locals of this stack frame.
    pub fn locals(&self) -> &[VerificationType] {
        &self.locals
    }

    /// Returns the stack of this stack frame.
    pub fn stack(&self) -> &[VerificationType] {
        &self.stack
    }
}

impl StackFrame {
    /// Creates the implicit stack frame for the given method.
    /// This frame is never written to the stack map table, since the JVM infers it.
    pub fn create_entry(class: &mut ClassFile, method: &Method) -> VerifyResult<Self> {
        let mut locals = Vec::new();
        let stack = Vec::new();

        // If the class is not static, add `this` to locals.
        if !method.access_flags.contains(MethodAccessFlags::STATIC) {
            // The type of `this` is uninitialized if this method is a constructor.
            if method.name == "<init>" {
                locals.push(VerificationType::UninitializedThis);
            } else {
                // Otherwise, it's a constant class reference to the class itself.
                locals.push(VerificationType::Object {
                    cpool_index: class.this_class,
                });
            }
        }

        // Add all of the method parameters to locals.
        for field_type in &method.parameters {
            let (verification_type, is_wide_type) =
                field_type_to_verification_type(&mut class.constant_pool, field_type)?;

            locals.push(verification_type);
            // Some types (such as double and long) are wide types and need padding on the stack.
            if is_wide_type {
                locals.push(VerificationType::Top);
            }
        }

        Ok(Self { locals, stack })
    }

    /// Describes a type mismatch between two stack frames.
    pub fn describe_mismatch(&self, other: &Self, index: u16, instruction: &Instruction) -> String {
        format!("\n\tinstruction at #{index}: {instruction}\n\tstack frame 1:\n\t\t{self:#?}\n\tstack frame 2:\n\t\t{other:#?}")
    }

    /// Resets the stack and pushes the given values.
    pub fn reset_with_initial_stack(&mut self, stack: Vec<VerificationType>) {
        self.stack = stack;
    }

    /// Simulate the stack operations of the given instruction.
    ///
    /// This function takes a mutable reference to a stack frame, a so called "entry frame".
    /// If the instruction modified the stack, the entry frame is updated to reflect the changes.
    /// It then becomes an "exit frame" and returns the outcome of the instruction.
    pub fn simulate_execution(
        &mut self,
        pool: &mut ConstantPool,
        instruction_index: u16,
        instruction: &Instruction,
    ) -> VerifyResult<ControlFlowOutcome> {
        Ok(match instruction {
            Instruction::Nop => ControlFlowOutcome::Continue,
            Instruction::Aconst_null => push_continue!(self, Null),
            Instruction::Iconst_m1
            | Instruction::Iconst_0
            | Instruction::Iconst_1
            | Instruction::Iconst_2
            | Instruction::Iconst_3
            | Instruction::Iconst_4
            | Instruction::Iconst_5 => push_continue!(self, Integer),
            Instruction::Lconst_0 | Instruction::Lconst_1 => push_continue!(self, [Long, Top]),
            Instruction::Fconst_0 | Instruction::Fconst_1 | Instruction::Fconst_2 => {
                push_continue!(self, Float)
            }
            Instruction::Dconst_0 | Instruction::Dconst_1 => {
                push_continue!(self, [Double, Top])
            }
            Instruction::Bipush(_) | Instruction::Sipush(_) => push_continue!(self, Integer),
            Instruction::Ldc(constant_index) => self.simulate_load_constant(
                instruction,
                instruction_index,
                pool,
                u16::from(*constant_index),
            )?,
            Instruction::Ldc_w(constant_index) | Instruction::Ldc2_w(constant_index) => {
                self.simulate_load_constant(instruction, instruction_index, pool, *constant_index)?
            }
            Instruction::Iload(local_index) => self.simulate_load(
                instruction,
                instruction_index,
                VerificationType::Integer,
                *local_index,
            )?,
            Instruction::Lload(local_index) => self.simulate_load(
                instruction,
                instruction_index,
                VerificationType::Long,
                *local_index,
            )?,
            Instruction::Fload(local_index) => self.simulate_load(
                instruction,
                instruction_index,
                VerificationType::Float,
                *local_index,
            )?,
            Instruction::Dload(local_index) => self.simulate_load(
                instruction,
                instruction_index,
                VerificationType::Double,
                *local_index,
            )?,
            Instruction::Aload(local_index) => {
                self.simulate_load_reference(instruction, instruction_index, *local_index)?
            }
            Instruction::Iload_0 => {
                self.simulate_load(instruction, instruction_index, VerificationType::Integer, 0)?
            }
            Instruction::Iload_1 => {
                self.simulate_load(instruction, instruction_index, VerificationType::Integer, 1)?
            }
            Instruction::Iload_2 => {
                self.simulate_load(instruction, instruction_index, VerificationType::Integer, 2)?
            }
            Instruction::Iload_3 => {
                self.simulate_load(instruction, instruction_index, VerificationType::Integer, 3)?
            }
            Instruction::Lload_0 => {
                self.simulate_load(instruction, instruction_index, VerificationType::Long, 0)?
            }
            Instruction::Lload_1 => {
                self.simulate_load(instruction, instruction_index, VerificationType::Long, 1)?
            }
            Instruction::Lload_2 => {
                self.simulate_load(instruction, instruction_index, VerificationType::Long, 2)?
            }
            Instruction::Lload_3 => {
                self.simulate_load(instruction, instruction_index, VerificationType::Long, 3)?
            }
            Instruction::Fload_0 => {
                self.simulate_load(instruction, instruction_index, VerificationType::Float, 0)?
            }
            Instruction::Fload_1 => {
                self.simulate_load(instruction, instruction_index, VerificationType::Float, 1)?
            }
            Instruction::Fload_2 => {
                self.simulate_load(instruction, instruction_index, VerificationType::Float, 2)?
            }
            Instruction::Fload_3 => {
                self.simulate_load(instruction, instruction_index, VerificationType::Float, 3)?
            }
            Instruction::Dload_0 => {
                self.simulate_load(instruction, instruction_index, VerificationType::Double, 0)?
            }
            Instruction::Dload_1 => {
                self.simulate_load(instruction, instruction_index, VerificationType::Double, 1)?
            }
            Instruction::Dload_2 => {
                self.simulate_load(instruction, instruction_index, VerificationType::Double, 2)?
            }
            Instruction::Dload_3 => {
                self.simulate_load(instruction, instruction_index, VerificationType::Double, 3)?
            }
            Instruction::Aload_0 => {
                self.simulate_load_reference(instruction, instruction_index, 0)?
            }
            Instruction::Aload_1 => {
                self.simulate_load_reference(instruction, instruction_index, 1)?
            }
            Instruction::Aload_2 => {
                self.simulate_load_reference(instruction, instruction_index, 2)?
            }
            Instruction::Aload_3 => {
                self.simulate_load_reference(instruction, instruction_index, 3)?
            }
            Instruction::Iaload => {
                self.simulate_load_array(instruction, instruction_index, pool)?
            }
            Instruction::Laload => {
                self.simulate_load_array(instruction, instruction_index, pool)?
            }
            Instruction::Faload => {
                self.simulate_load_array(instruction, instruction_index, pool)?
            }
            Instruction::Daload => {
                self.simulate_load_array(instruction, instruction_index, pool)?
            }
            Instruction::Aaload => {
                self.simulate_load_array(instruction, instruction_index, pool)?
            }
            Instruction::Baload => {
                self.simulate_load_array(instruction, instruction_index, pool)?
            }
            Instruction::Caload => {
                self.simulate_load_array(instruction, instruction_index, pool)?
            }
            Instruction::Saload => {
                self.simulate_load_array(instruction, instruction_index, pool)?
            }
            Instruction::Istore(local_index) => self.simulate_store(
                instruction,
                instruction_index,
                VerificationType::Integer,
                *local_index,
            )?,
            Instruction::Lstore(local_index) => self.simulate_store(
                instruction,
                instruction_index,
                VerificationType::Long,
                *local_index,
            )?,
            Instruction::Fstore(local_index) => self.simulate_store(
                instruction,
                instruction_index,
                VerificationType::Float,
                *local_index,
            )?,
            Instruction::Dstore(local_index) => self.simulate_store(
                instruction,
                instruction_index,
                VerificationType::Double,
                *local_index,
            )?,
            Instruction::Astore(local_index) => {
                self.simulate_store_reference(instruction, instruction_index, *local_index)?
            }
            Instruction::Istore_0 => {
                self.simulate_store(instruction, instruction_index, VerificationType::Integer, 0)?
            }
            Instruction::Istore_1 => {
                self.simulate_store(instruction, instruction_index, VerificationType::Integer, 1)?
            }
            Instruction::Istore_2 => {
                self.simulate_store(instruction, instruction_index, VerificationType::Integer, 2)?
            }
            Instruction::Istore_3 => {
                self.simulate_store(instruction, instruction_index, VerificationType::Integer, 3)?
            }
            Instruction::Lstore_0 => {
                self.simulate_store(instruction, instruction_index, VerificationType::Long, 0)?
            }
            Instruction::Lstore_1 => {
                self.simulate_store(instruction, instruction_index, VerificationType::Long, 1)?
            }
            Instruction::Lstore_2 => {
                self.simulate_store(instruction, instruction_index, VerificationType::Long, 2)?
            }
            Instruction::Lstore_3 => {
                self.simulate_store(instruction, instruction_index, VerificationType::Long, 3)?
            }
            Instruction::Fstore_0 => {
                self.simulate_store(instruction, instruction_index, VerificationType::Float, 0)?
            }
            Instruction::Fstore_1 => {
                self.simulate_store(instruction, instruction_index, VerificationType::Float, 1)?
            }
            Instruction::Fstore_2 => {
                self.simulate_store(instruction, instruction_index, VerificationType::Float, 2)?
            }
            Instruction::Fstore_3 => {
                self.simulate_store(instruction, instruction_index, VerificationType::Float, 3)?
            }
            Instruction::Dstore_0 => {
                self.simulate_store(instruction, instruction_index, VerificationType::Double, 0)?
            }
            Instruction::Dstore_1 => {
                self.simulate_store(instruction, instruction_index, VerificationType::Double, 1)?
            }
            Instruction::Dstore_2 => {
                self.simulate_store(instruction, instruction_index, VerificationType::Double, 2)?
            }
            Instruction::Dstore_3 => {
                self.simulate_store(instruction, instruction_index, VerificationType::Double, 3)?
            }
            Instruction::Astore_0 => {
                self.simulate_store_reference(instruction, instruction_index, 0)?
            }
            Instruction::Astore_1 => {
                self.simulate_store_reference(instruction, instruction_index, 1)?
            }
            Instruction::Astore_2 => {
                self.simulate_store_reference(instruction, instruction_index, 2)?
            }
            Instruction::Astore_3 => {
                self.simulate_store_reference(instruction, instruction_index, 3)?
            }
            Instruction::Iastore => {
                self.simulate_store_array(instruction, instruction_index, false)?
            }
            Instruction::Lastore => {
                self.simulate_store_array(instruction, instruction_index, true)?
            }
            Instruction::Fastore => {
                self.simulate_store_array(instruction, instruction_index, false)?
            }
            Instruction::Dastore => {
                self.simulate_store_array(instruction, instruction_index, true)?
            }
            Instruction::Aastore => {
                self.simulate_store_array(instruction, instruction_index, false)?
            }
            Instruction::Bastore => {
                self.simulate_store_array(instruction, instruction_index, false)?
            }
            Instruction::Castore => {
                self.simulate_store_array(instruction, instruction_index, false)?
            }
            Instruction::Sastore => {
                self.simulate_store_array(instruction, instruction_index, false)?
            }
            Instruction::Pop => self.simulate_stack_manipulation(instruction, instruction_index)?,
            Instruction::Pop2 => {
                self.simulate_stack_manipulation(instruction, instruction_index)?
            }
            Instruction::Dup => self.simulate_stack_manipulation(instruction, instruction_index)?,
            Instruction::Dup_x1 => {
                self.simulate_stack_manipulation(instruction, instruction_index)?
            }
            Instruction::Dup_x2 => {
                self.simulate_stack_manipulation(instruction, instruction_index)?
            }
            Instruction::Dup2 => {
                self.simulate_stack_manipulation(instruction, instruction_index)?
            }
            Instruction::Dup2_x1 => {
                self.simulate_stack_manipulation(instruction, instruction_index)?
            }
            Instruction::Dup2_x2 => {
                self.simulate_stack_manipulation(instruction, instruction_index)?
            }
            Instruction::Swap => {
                self.simulate_stack_manipulation(instruction, instruction_index)?
            }
            Instruction::Iadd => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Integer,
                2,
            )?,
            Instruction::Ladd => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Long,
                2,
            )?,
            Instruction::Fadd => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Float,
                2,
            )?,
            Instruction::Dadd => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Double,
                2,
            )?,
            Instruction::Isub => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Integer,
                2,
            )?,
            Instruction::Lsub => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Long,
                2,
            )?,
            Instruction::Fsub => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Float,
                2,
            )?,
            Instruction::Dsub => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Double,
                2,
            )?,
            Instruction::Imul => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Integer,
                2,
            )?,
            Instruction::Lmul => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Long,
                2,
            )?,
            Instruction::Fmul => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Float,
                2,
            )?,
            Instruction::Dmul => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Double,
                2,
            )?,
            Instruction::Idiv => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Integer,
                2,
            )?,
            Instruction::Ldiv => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Long,
                2,
            )?,
            Instruction::Fdiv => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Float,
                2,
            )?,
            Instruction::Ddiv => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Double,
                2,
            )?,
            Instruction::Irem => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Integer,
                2,
            )?,
            Instruction::Lrem => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Long,
                2,
            )?,
            Instruction::Frem => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Float,
                2,
            )?,
            Instruction::Drem => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Double,
                2,
            )?,
            Instruction::Ineg => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Integer,
                1,
            )?,
            Instruction::Lneg => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Long,
                1,
            )?,
            Instruction::Fneg => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Float,
                1,
            )?,
            Instruction::Dneg => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Double,
                1,
            )?,
            Instruction::Ishl => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Integer,
                2,
            )?,
            Instruction::Lshl => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Long,
                2,
            )?,
            Instruction::Ishr => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Integer,
                2,
            )?,
            Instruction::Lshr => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Long,
                2,
            )?,
            Instruction::Iushr => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Integer,
                2,
            )?,
            Instruction::Lushr => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Long,
                2,
            )?,
            Instruction::Iand => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Integer,
                2,
            )?,
            Instruction::Land => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Long,
                2,
            )?,
            Instruction::Ior => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Integer,
                2,
            )?,
            Instruction::Lor => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Long,
                2,
            )?,
            Instruction::Ixor => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Integer,
                2,
            )?,
            Instruction::Lxor => self.simulate_number_arithmetic(
                instruction,
                instruction_index,
                VerificationType::Long,
                2,
            )?,
            Instruction::Iinc(local_index, _) => {
                self.simulate_increment_by_value(instruction, instruction_index, *local_index)?
            }
            Instruction::I2l => self.simulate_number_conversion(
                instruction,
                instruction_index,
                VerificationType::Integer,
                VerificationType::Long,
            )?,
            Instruction::I2f => self.simulate_number_conversion(
                instruction,
                instruction_index,
                VerificationType::Integer,
                VerificationType::Float,
            )?,
            Instruction::I2d => self.simulate_number_conversion(
                instruction,
                instruction_index,
                VerificationType::Integer,
                VerificationType::Double,
            )?,
            Instruction::L2i => self.simulate_number_conversion(
                instruction,
                instruction_index,
                VerificationType::Long,
                VerificationType::Integer,
            )?,
            Instruction::L2f => self.simulate_number_conversion(
                instruction,
                instruction_index,
                VerificationType::Long,
                VerificationType::Float,
            )?,
            Instruction::L2d => self.simulate_number_conversion(
                instruction,
                instruction_index,
                VerificationType::Long,
                VerificationType::Double,
            )?,
            Instruction::F2i => self.simulate_number_conversion(
                instruction,
                instruction_index,
                VerificationType::Float,
                VerificationType::Integer,
            )?,
            Instruction::F2l => self.simulate_number_conversion(
                instruction,
                instruction_index,
                VerificationType::Float,
                VerificationType::Long,
            )?,
            Instruction::F2d => self.simulate_number_conversion(
                instruction,
                instruction_index,
                VerificationType::Float,
                VerificationType::Double,
            )?,
            Instruction::D2i => self.simulate_number_conversion(
                instruction,
                instruction_index,
                VerificationType::Double,
                VerificationType::Integer,
            )?,
            Instruction::D2l => self.simulate_number_conversion(
                instruction,
                instruction_index,
                VerificationType::Double,
                VerificationType::Long,
            )?,
            Instruction::D2f => self.simulate_number_conversion(
                instruction,
                instruction_index,
                VerificationType::Double,
                VerificationType::Float,
            )?,
            Instruction::I2b => self.simulate_number_conversion(
                instruction,
                instruction_index,
                VerificationType::Integer,
                VerificationType::Integer,
            )?,
            Instruction::I2c => self.simulate_number_conversion(
                instruction,
                instruction_index,
                VerificationType::Integer,
                VerificationType::Integer,
            )?,
            Instruction::I2s => self.simulate_number_conversion(
                instruction,
                instruction_index,
                VerificationType::Integer,
                VerificationType::Integer,
            )?,
            Instruction::Lcmp => self.simulate_numeric_comparison(
                instruction,
                instruction_index,
                VerificationType::Long,
            )?,
            Instruction::Fcmpl => self.simulate_numeric_comparison(
                instruction,
                instruction_index,
                VerificationType::Float,
            )?,
            Instruction::Fcmpg => self.simulate_numeric_comparison(
                instruction,
                instruction_index,
                VerificationType::Float,
            )?,
            Instruction::Dcmpl => self.simulate_numeric_comparison(
                instruction,
                instruction_index,
                VerificationType::Double,
            )?,
            Instruction::Dcmpg => self.simulate_numeric_comparison(
                instruction,
                instruction_index,
                VerificationType::Double,
            )?,
            Instruction::Ifeq(offset) => {
                self.simulate_if_statement(instruction, instruction_index, *offset)?
            }
            Instruction::Ifne(offset) => {
                self.simulate_if_statement(instruction, instruction_index, *offset)?
            }
            Instruction::Iflt(offset) => {
                self.simulate_if_statement(instruction, instruction_index, *offset)?
            }
            Instruction::Ifge(offset) => {
                self.simulate_if_statement(instruction, instruction_index, *offset)?
            }
            Instruction::Ifgt(offset) => {
                self.simulate_if_statement(instruction, instruction_index, *offset)?
            }
            Instruction::Ifle(offset) => {
                self.simulate_if_statement(instruction, instruction_index, *offset)?
            }
            Instruction::If_icmpeq(offset) => {
                self.simulate_ifcmp_statement(instruction, instruction_index, false, *offset)?
            }
            Instruction::If_icmpne(offset) => {
                self.simulate_ifcmp_statement(instruction, instruction_index, false, *offset)?
            }
            Instruction::If_icmplt(offset) => {
                self.simulate_ifcmp_statement(instruction, instruction_index, false, *offset)?
            }
            Instruction::If_icmpge(offset) => {
                self.simulate_ifcmp_statement(instruction, instruction_index, false, *offset)?
            }
            Instruction::If_icmpgt(offset) => {
                self.simulate_ifcmp_statement(instruction, instruction_index, false, *offset)?
            }
            Instruction::If_icmple(offset) => {
                self.simulate_ifcmp_statement(instruction, instruction_index, false, *offset)?
            }
            Instruction::If_acmpeq(offset) => {
                self.simulate_ifcmp_statement(instruction, instruction_index, true, *offset)?
            }
            Instruction::If_acmpne(offset) => {
                self.simulate_ifcmp_statement(instruction, instruction_index, true, *offset)?
            }
            Instruction::Goto(offset) => ControlFlowOutcome::Jump(*offset),
            Instruction::Tableswitch {
                default,
                low,
                high,
                offsets: switch_offsets,
            } => {
                let mut offsets = vec![*default];
                offsets.extend_from_slice(switch_offsets);
                self.simulate_switch_statement(instruction, instruction_index, offsets)?
            }
            Instruction::Lookupswitch { default, pairs } => {
                let mut offsets = pairs.values().cloned().collect::<Vec<_>>();
                offsets.insert(0, *default);
                self.simulate_switch_statement(instruction, instruction_index, offsets)?
            }
            Instruction::Ireturn => self.simulate_return(
                instruction,
                instruction_index,
                Some(VerificationType::Integer),
            )?,
            Instruction::Lreturn => {
                self.simulate_return(instruction, instruction_index, Some(VerificationType::Long))?
            }
            Instruction::Freturn => self.simulate_return(
                instruction,
                instruction_index,
                Some(VerificationType::Float),
            )?,
            Instruction::Dreturn => self.simulate_return(
                instruction,
                instruction_index,
                Some(VerificationType::Double),
            )?,
            Instruction::Areturn => {
                self.simulate_return_reference(instruction, instruction_index)?
            }
            Instruction::Return => self.simulate_return(instruction, instruction_index, None)?,
            Instruction::Getstatic(field_index) => {
                self.simulate_get_field(instruction, instruction_index, pool, true, *field_index)?
            }
            Instruction::Putstatic(field_index) => {
                self.simulate_put_field(instruction, instruction_index, pool, true, *field_index)?
            }
            Instruction::Getfield(field_index) => {
                self.simulate_get_field(instruction, instruction_index, pool, false, *field_index)?
            }
            Instruction::Putfield(field_index) => {
                self.simulate_put_field(instruction, instruction_index, pool, false, *field_index)?
            }
            Instruction::Invokevirtual(method_index) => self.simulate_method_call(
                instruction,
                instruction_index,
                pool,
                false,
                false,
                *method_index,
            )?,
            Instruction::Invokespecial(method_index) => self.simulate_method_call(
                instruction,
                instruction_index,
                pool,
                false,
                false,
                *method_index,
            )?,
            Instruction::Invokestatic(method_index) => self.simulate_method_call(
                instruction,
                instruction_index,
                pool,
                true,
                false,
                *method_index,
            )?,
            Instruction::Invokeinterface(method_index, _) => self.simulate_method_call(
                instruction,
                instruction_index,
                pool,
                false,
                false,
                *method_index,
            )?,
            Instruction::Invokedynamic(callsite_index) => self.simulate_method_call(
                instruction,
                instruction_index,
                pool,
                true,
                true,
                *callsite_index,
            )?,
            Instruction::New(class_index) => {
                self.simulate_new(instruction, instruction_index, pool, *class_index)?
            }
            Instruction::Newarray(array_type) => {
                self.simulate_new_array(instruction, instruction_index, pool, array_type)?
            }
            Instruction::Anewarray(class_index) => self.simulate_new_array_reference(
                instruction,
                instruction_index,
                pool,
                *class_index,
                1,
            )?,
            Instruction::Arraylength => {
                self.simulate_array_length(instruction, instruction_index)?
            }
            Instruction::Athrow => self.simulate_throw(instruction, instruction_index)?,
            Instruction::Checkcast(class_index) => {
                self.simulate_checkcast(instruction, instruction_index, pool, *class_index)?
            }
            Instruction::Instanceof(class_index) => {
                self.simulate_instanceof(instruction, instruction_index, pool, *class_index)?
            }
            Instruction::Monitorenter | Instruction::Monitorexit => {
                self.simulate_monitor_operation(instruction, instruction_index)?
            }
            Instruction::Multianewarray(class_index, dimensions) => self
                .simulate_new_array_reference(
                    instruction,
                    instruction_index,
                    pool,
                    *class_index,
                    *dimensions,
                )?,
            Instruction::Ifnull(offset) => {
                self.simulate_if_reference_statement(instruction, instruction_index, *offset)?
            }
            Instruction::Ifnonnull(offset) => {
                self.simulate_if_reference_statement(instruction, instruction_index, *offset)?
            }
            Instruction::Goto_w(offset) => {
                // As of writing, the maximum instructions length is 65535.
                // This means that the offset can fit safely within a u16.
                match u16::try_from(*offset) {
                    Ok(offset) => ControlFlowOutcome::Jump(offset),
                    Err(_) => return error!(instruction_index, instruction),
                }
            }
            Instruction::Iload_w(local_index) => self.simulate_load(
                instruction,
                instruction_index,
                VerificationType::Integer,
                *local_index,
            )?,
            Instruction::Lload_w(local_index) => self.simulate_load(
                instruction,
                instruction_index,
                VerificationType::Long,
                *local_index,
            )?,
            Instruction::Fload_w(local_index) => self.simulate_load(
                instruction,
                instruction_index,
                VerificationType::Float,
                *local_index,
            )?,
            Instruction::Dload_w(local_index) => self.simulate_load(
                instruction,
                instruction_index,
                VerificationType::Double,
                *local_index,
            )?,
            Instruction::Aload_w(local_index) => {
                self.simulate_load_reference(instruction, instruction_index, *local_index)?
            }
            Instruction::Istore_w(local_index) => self.simulate_store(
                instruction,
                instruction_index,
                VerificationType::Integer,
                *local_index,
            )?,
            Instruction::Lstore_w(local_index) => self.simulate_store(
                instruction,
                instruction_index,
                VerificationType::Long,
                *local_index,
            )?,
            Instruction::Fstore_w(local_index) => self.simulate_store(
                instruction,
                instruction_index,
                VerificationType::Float,
                *local_index,
            )?,
            Instruction::Dstore_w(local_index) => self.simulate_store(
                instruction,
                instruction_index,
                VerificationType::Double,
                *local_index,
            )?,
            Instruction::Astore_w(local_index) => {
                self.simulate_store_reference(instruction, instruction_index, *local_index)?
            }
            Instruction::Iinc_w(local_index, _) => {
                self.simulate_increment_by_value(instruction, instruction_index, *local_index)?
            }
            // These instructions are deprecated and would otherwise complicate the CFG.
            // "ret" is not to be confused with "return", which is a different instruction.
            Instruction::Jsr(_)
            | Instruction::Jsr_w(_)
            | Instruction::Ret(_)
            | Instruction::Ret_w(_) => {
                return Err(VerificationError::UnsupportedInstruction(
                    instruction_index,
                    instruction.clone(),
                ))
            }
            // These instructions are reserved for debugging and implementation dependent operations.
            Instruction::Breakpoint | Instruction::Impdep1 | Instruction::Impdep2 => {
                return Err(VerificationError::UnsupportedInstruction(
                    instruction_index,
                    instruction.clone(),
                ))
            }
            // This instruction should never be read, since it's suffixed (_s) counterparts should be used.
            // This probably signals a bug in the ristretto_classfile crate.
            Instruction::Wide => {
                return Err(VerificationError::UnsupportedInstruction(
                    instruction_index,
                    instruction.clone(),
                ))
            }
        })
    }

    // TODO: certain instructions don't allow double and long, so verify that

    fn simulate_load_constant(
        &mut self,
        instruction: &Instruction,
        instruction_index: u16,
        pool: &mut ConstantPool,
        constant_index: u16,
    ) -> VerifyResult<ControlFlowOutcome> {
        match pool.get(constant_index) {
            None => error!(instruction_index, instruction),
            Some(constant) => Ok(match constant {
                Constant::Integer(_) => push_continue!(self, Integer),
                Constant::Float(_) => push_continue!(self, Float),
                Constant::Long(_) => {
                    // Only ldc2_w can push a long onto the stack.
                    if !matches!(instruction, Instruction::Ldc2_w(_)) {
                        return error!(instruction_index, instruction);
                    }
                    // If allowed, push the long onto the stack.
                    push_continue!(self, [Long, Top])
                }
                Constant::Double(_) => {
                    // Only ldc2_w can push a double onto the stack.
                    if !matches!(instruction, Instruction::Ldc2_w(_)) {
                        return error!(instruction_index, instruction);
                    }
                    // If allowed, push the double onto the stack.
                    push_continue!(self, [Double, Top])
                }
                Constant::String(utf8_index) => {
                    // A string value is always pushed as a java/lang/String reference.
                    push_continue!(self object get_string_reference(pool)?)
                }
                // The following constants are all passed by reference on the stack.
                Constant::Class(_)
                | Constant::MethodHandle { .. }
                | Constant::MethodType(_)
                | Constant::Dynamic { .. } => push_continue!(self object constant_index),
                // The rest of the constants are not supported by this instruction.
                _ => return error!(instruction_index, instruction),
            }),
        }
    }

    fn simulate_load<N: TryInto<u16>>(
        &mut self,
        instruction: &Instruction,
        instruction_index: u16,
        ty: VerificationType,
        local_index: N,
    ) -> VerifyResult<ControlFlowOutcome> {
        let mut local_index = short_index!(local_index, instruction_index, instruction);
        // Wide types are padded, so decrement the local index.
        if is_wide_type(&ty) {
            // Verify that the wide type is actually padded.
            try_get_local!(
                self,
                instruction_index,
                instruction,
                local_index + 1,
                VerificationType::Top
            )?;
        }
        // Get the local variable by the given index and required type, and push it to the stack.
        self.stack.push(
            try_get_local_eq!(self, instruction_index, instruction, local_index, &ty)?.clone(),
        );
        // Wide types require padding on the stack.
        if is_wide_type(&ty) {
            self.stack.push(VerificationType::Top);
        }
        // Continue.
        Ok(ControlFlowOutcome::Continue)
    }

    fn simulate_load_reference<N: TryInto<u16>>(
        &mut self,
        instruction: &Instruction,
        instruction_index: u16,
        local_index: N,
    ) -> VerifyResult<ControlFlowOutcome> {
        let local_index = short_index!(local_index, instruction_index, instruction);
        // Get the local variable by the given index, and push it to the stack.
        self.stack.push(
            try_get_local!(
                self,
                instruction_index,
                instruction,
                local_index,
                VerificationType::Object { .. }
            )?
            .clone(),
        );
        // Continue.
        Ok(ControlFlowOutcome::Continue)
    }

    fn simulate_load_array(
        &mut self,
        instruction: &Instruction,
        instruction_index: u16,
        pool: &mut ConstantPool,
    ) -> VerifyResult<ControlFlowOutcome> {
        // Pop the index off the stack.
        try_pop_stack!(
            self,
            instruction_index,
            instruction,
            VerificationType::Integer
        )?;
        // Pop the array reference off the stack.
        let array_reference = try_pop_stack!(
            self,
            instruction_index,
            instruction,
            VerificationType::Object { .. }
        )?;
        // Parse the array reference descriptor.
        let (array_element_type, is_wide_type) = parse_array_reference(pool, array_reference)?;
        // Push the element type onto the stack.
        self.stack.push(array_element_type);
        // Wide types require padding on the stack.
        if is_wide_type {
            self.stack.push(VerificationType::Top);
        }
        // Continue.
        Ok(ControlFlowOutcome::Continue)
    }

    fn simulate_store<N: TryInto<u16>>(
        &mut self,
        instruction: &Instruction,
        instruction_index: u16,
        ty: VerificationType,
        local_index: N,
    ) -> VerifyResult<ControlFlowOutcome> {
        let local_index = short_index!(local_index, instruction_index, instruction);
        // Pop the value that should be stored from the stack.
        let value = try_pop_stack_checked!(self, instruction_index, instruction, ty)?;
        // Store the value at the given index.
        try_set_local!(self, instruction_index, instruction, local_index, value)?;
        // Wide types require padding, so add padding into the next local variable.
        if is_wide_type(&ty) {
            try_set_local!(
                self,
                instruction_index,
                instruction,
                local_index + 1,
                VerificationType::Top
            )?;
        }
        // Continue.
        Ok(ControlFlowOutcome::Continue)
    }

    fn simulate_store_reference<N: TryInto<u16>>(
        &mut self,
        instruction: &Instruction,
        instruction_index: u16,
        local_index: N,
    ) -> VerifyResult<ControlFlowOutcome> {
        let local_index = short_index!(local_index, instruction_index, instruction);
        // Pop the value that should be stored from the stack.
        let value = try_pop_stack!(
            self,
            instruction_index,
            instruction,
            VerificationType::Object { .. }
        )?;
        // Store the value at the given index.
        try_set_local!(self, instruction_index, instruction, local_index, value)?;
        // Continue.
        Ok(ControlFlowOutcome::Continue)
    }

    fn simulate_store_array(
        &mut self,
        instruction: &Instruction,
        instruction_index: u16,
        is_wide_type: bool,
    ) -> VerifyResult<ControlFlowOutcome> {
        // Pop the value that should be stored from the stack.
        try_pop_stack_checked!(self, instruction_index, instruction);
        // Pop the index where the value should be stored from the stack.
        try_pop_stack_eq!(
            self,
            instruction_index,
            instruction,
            VerificationType::Integer
        );
        // Pop the array reference from the stack.
        try_pop_stack!(
            self,
            instruction_index,
            instruction,
            VerificationType::Object { .. }
        )?;
        // Continue.
        Ok(ControlFlowOutcome::Continue)
    }

    fn simulate_stack_manipulation(
        &mut self,
        instruction: &Instruction,
        instruction_index: u16,
    ) -> VerifyResult<ControlFlowOutcome> {
        match instruction {
            Instruction::Pop => {
                try_pop_stack!(self, instruction_index, instruction)?;
            }
            Instruction::Pop2 => {
                try_pop_stack_n!(self, instruction_index, instruction, 2[noreturn])?;
            }
            Instruction::Dup => {
                // Duplicate the top stack element.
                match self.stack.last().cloned() {
                    Some(value) => self.stack.push(value),
                    None => return error!(instruction_index, instruction),
                }
            }
            Instruction::Dup_x1 => {
                // Both value types must be a category 1 type.
                let [value2, value1] = try_pop_stack_n!(self, instruction_index, instruction, 2)?;
                if is_wide_type(&value1) || is_wide_type(&value2) {
                    return error!(instruction_index, instruction);
                }
                // Duplicate the top value and insert it below the second value.
                self.stack
                    .extend_from_slice(&[value1.clone(), value2, value1]);
            }
            Instruction::Dup_x2 => {
                // Types must be either [C1, C1, C1] or [C2, Top, C1].
                let [value3, value2, value1] =
                    try_pop_stack_n!(self, instruction_index, instruction, 3)?;
                // First value must be a category 1 type.
                if is_wide_type(&value1) {
                    return error!(instruction_index, instruction);
                }
                // Verify the category 2 type if it exists.
                if is_wide_type_invalid(&value2, &value3) {
                    return error!(instruction_index, instruction);
                }
                // Duplicate the top value and insert it below the third value.
                self.stack
                    .extend_from_slice(&[value1.clone(), value3, value2, value1]);
            }
            Instruction::Dup2 => {
                // Types must be either [C1, C1] or [C2, Top].
                let [value2, value1] = try_pop_stack_n!(self, instruction_index, instruction, 2)?;
                // Verify the category 2 type if it exists.
                if is_wide_type_invalid(&value2, &value1) {
                    return error!(instruction_index, instruction);
                }
                // Duplicate the top two values and insert them below the second value.
                self.stack
                    .extend_from_slice(&[value2.clone(), value1.clone(), value2, value1]);
            }
            Instruction::Dup2_x1 => {
                // Types must be either [C1, C1, C1] or [C1, C2, Top].
                let [value3, value2, value1] =
                    try_pop_stack_n!(self, instruction_index, instruction, 3)?;
                // Third value must be a category 1 type.
                if is_wide_type(&value3) {
                    return error!(instruction_index, instruction);
                }
                // Verify the category 2 type if it exists.
                if is_wide_type_invalid(&value2, &value1) {
                    return error!(instruction_index, instruction);
                }
                // Duplicate the top two values and insert them below the third value.
                self.stack.extend_from_slice(&[
                    value2.clone(),
                    value1.clone(),
                    value3,
                    value2,
                    value1,
                ]);
            }
            Instruction::Dup2_x2 => {
                // Types must be either [C1, C1, C1, C1] or [C2, Top, C1, C1].
                let [value4, value3, value2, value1] =
                    try_pop_stack_n!(self, instruction_index, instruction, 4)?;
                // First and second value must be a category 1 type.
                if is_wide_type(&value2) || is_wide_type(&value1) {
                    return error!(instruction_index, instruction);
                }
                // Verify the category 2 type if it exists.
                if is_wide_type_invalid(&value4, &value3) {
                    return error!(instruction_index, instruction);
                }
                // Duplicate the top two values and insert them below the fourth value.
                self.stack.extend_from_slice(&[
                    value2.clone(),
                    value1.clone(),
                    value4,
                    value3,
                    value2,
                    value1,
                ]);
            }
            Instruction::Swap => {
                // Make sure the stack has at least 2 elements.
                if self.stack.len() < 2 {
                    return error!(instruction_index, instruction);
                }
                // Swap the top two stack elements.
                let len = self.stack.len() - 1;
                self.stack.swap(len - 1, len);
            }
            _ => unreachable!(),
        }

        // Continue.
        Ok(ControlFlowOutcome::Continue)
    }

    fn simulate_number_arithmetic(
        &mut self,
        instruction: &Instruction,
        instruction_index: u16,
        ty: VerificationType,
        input_count: u8,
    ) -> VerifyResult<ControlFlowOutcome> {
        // Pop the input values from the stack as specified by the instruction.
        for _ in 0..input_count {
            let value = try_pop_stack_checked!(self, instruction_index, instruction, ty)?;
            // Check that the stack contains the valid type for this instruction.
            if value != ty {
                return error!(instruction_index, instruction);
            }
        }
        // Push the result value onto the stack.
        self.stack.push(ty.clone());
        // Wide types require padding on the stack.
        if is_wide_type(&ty) {
            self.stack.push(VerificationType::Top);
        }
        // Continue.
        Ok(ControlFlowOutcome::Continue)
    }

    fn simulate_number_conversion(
        &mut self,
        instruction: &Instruction,
        instruction_index: u16,
        from_ty: VerificationType,
        to_ty: VerificationType,
    ) -> VerifyResult<ControlFlowOutcome> {
        // Pop the input value from the stack.
        try_pop_stack_checked!(self, instruction_index, instruction, from_ty)?;
        // Push the result value onto the stack.
        self.stack.push(to_ty.clone());
        // Wide types require padding on the stack.
        if is_wide_type(&to_ty) {
            self.stack.push(VerificationType::Top);
        }
        // Continue.
        Ok(ControlFlowOutcome::Continue)
    }

    fn simulate_increment_by_value<N: TryInto<u16>>(
        &mut self,
        instruction: &Instruction,
        instruction_index: u16,
        local_index: N,
    ) -> VerifyResult<ControlFlowOutcome> {
        let local_index = short_index!(local_index, instruction_index, instruction);
        // Verify that the local variable at the given index is an integer.
        try_get_local!(
            self,
            instruction_index,
            instruction,
            local_index,
            VerificationType::Integer
        )?;
        // Continue.
        Ok(ControlFlowOutcome::Continue)
    }

    fn simulate_numeric_comparison(
        &mut self,
        instruction: &Instruction,
        instruction_index: u16,
        ty: VerificationType,
    ) -> VerifyResult<ControlFlowOutcome> {
        // Pop the two input values from the stack. Cannot use try_pop_stack_n!
        // here because it doesn't check for wide types.
        try_pop_stack_checked!(self, instruction_index, instruction, ty)?;
        try_pop_stack_checked!(self, instruction_index, instruction, ty)?;
        // Push the integer result value onto the stack.
        self.stack.push(VerificationType::Integer);
        // Continue.
        Ok(ControlFlowOutcome::Continue)
    }

    fn simulate_if_statement(
        &mut self,
        instruction: &Instruction,
        instruction_index: u16,
        offset: u16,
    ) -> VerifyResult<ControlFlowOutcome> {
        // Pop the integer value from the stack.
        try_pop_stack_eq!(
            self,
            instruction_index,
            instruction,
            VerificationType::Integer
        )?;
        // Branch to the given offset.
        Ok(ControlFlowOutcome::Branch(offset))
    }

    fn simulate_ifcmp_statement(
        &mut self,
        instruction: &Instruction,
        instruction_index: u16,
        is_reference: bool,
        offset: u16,
    ) -> VerifyResult<ControlFlowOutcome> {
        // Pop the two integer comparison values from the stack.
        for _ in 0..2 {
            if is_reference {
                try_pop_stack!(
                    self,
                    instruction_index,
                    instruction,
                    VerificationType::Object { .. }
                )?;
            } else {
                try_pop_stack_eq!(
                    self,
                    instruction_index,
                    instruction,
                    VerificationType::Integer
                )?;
            }
        }
        // Branch to the given offset.
        Ok(ControlFlowOutcome::Branch(offset))
    }

    fn simulate_if_reference_statement(
        &mut self,
        instruction: &Instruction,
        instruction_index: u16,
        offset: u16,
    ) -> VerifyResult<ControlFlowOutcome> {
        // Pop the integer value from the stack.
        try_pop_stack!(
            self,
            instruction_index,
            instruction,
            VerificationType::Object { .. }
        )?;
        // Branch to the given offset.
        Ok(ControlFlowOutcome::Branch(offset))
    }

    fn simulate_switch_statement(
        &mut self,
        instruction: &Instruction,
        instruction_index: u16,
        offsets: Vec<i32>,
    ) -> VerifyResult<ControlFlowOutcome> {
        // Convert the given offsets into something we can use.
        let offsets = offsets
            .into_iter()
            .map(|offset| {
                // As of writing, the maximum instructions length is 65535.
                // This means that the offset can fit safely within a u16.
                u16::try_from(offset).map_err(|_| error!([noerr] instruction_index, instruction))
            })
            .collect::<VerifyResult<_>>()?;
        // Pop the switch key/index from the stack.
        try_pop_stack_eq!(
            self,
            instruction_index,
            instruction,
            VerificationType::Integer
        )?;
        // Branch to any of the given offsets.
        Ok(ControlFlowOutcome::Switch(offsets))
    }

    fn simulate_return(
        &mut self,
        instruction: &Instruction,
        instruction_index: u16,
        ty: Option<VerificationType>,
    ) -> VerifyResult<ControlFlowOutcome> {
        // Pop the return value from the stack, if applicable.
        if let Some(ty) = ty {
            try_pop_stack_checked!(self, instruction_index, instruction, ty)?;
        }
        // Clear the stack frame.
        self.stack.clear();
        // Return from the method, ending execution.
        Ok(ControlFlowOutcome::Return)
    }

    fn simulate_return_reference(
        &mut self,
        instruction: &Instruction,
        instruction_index: u16,
    ) -> VerifyResult<ControlFlowOutcome> {
        // Pop the return value from the stack.
        try_pop_stack!(
            self,
            instruction_index,
            instruction,
            VerificationType::Object { .. }
        )?;
        // Clear the stack frame.
        self.stack.clear();
        // Return from the method, ending execution.
        Ok(ControlFlowOutcome::Return)
    }

    fn simulate_get_field(
        &mut self,
        instruction: &Instruction,
        instruction_index: u16,
        pool: &mut ConstantPool,
        is_static: bool,
        field_index: u16,
    ) -> VerifyResult<ControlFlowOutcome> {
        // Pop the object reference from the stack if this method is not static.
        if !is_static {
            try_pop_stack!(
                self,
                instruction_index,
                instruction,
                VerificationType::Object { .. }
            )?;
        }
        // Parse the field reference.
        let (field_type, is_wide_type) = parse_field_reference(pool, field_index)?;
        // Push the field value onto the stack.
        self.stack.push(field_type);
        // Wide types require padding on the stack.
        if is_wide_type {
            self.stack.push(VerificationType::Top);
        }
        // Continue.
        Ok(ControlFlowOutcome::Continue)
    }

    fn simulate_put_field(
        &mut self,
        instruction: &Instruction,
        instruction_index: u16,
        pool: &mut ConstantPool,
        is_static: bool,
        field_index: u16,
    ) -> VerifyResult<ControlFlowOutcome> {
        // Pop the field value from the stack.
        let value_type = try_pop_stack_checked!(self, instruction_index, instruction);
        // Pop the object reference from the stack if this method is not static.
        if !is_static {
            try_pop_stack!(
                self,
                instruction_index,
                instruction,
                VerificationType::Object { .. }
            )?;
        }
        // Parse the field reference.
        let (field_type, _) = parse_field_reference(pool, field_index)?;
        // Verify that the field type matches the value type.
        if field_type != value_type {
            return error!(instruction_index, instruction);
        }
        // Continue.
        Ok(ControlFlowOutcome::Continue)
    }

    fn simulate_method_call(
        &mut self,
        instruction: &Instruction,
        instruction_index: u16,
        pool: &mut ConstantPool,
        is_static: bool,
        is_dynamic: bool,
        method_or_callsite_index: u16,
    ) -> VerifyResult<ControlFlowOutcome> {
        // Resolve the method reference.
        let (parameters, return_type) =
            parse_method_reference(pool, is_dynamic, method_or_callsite_index)?;
        // Pop the arguments from the stack.
        for parameter in parameters {
            let argument = try_pop_stack_checked!(self, instruction_index, instruction, parameter)?;
            // Verify that the argument type matches the parameter type.
            if argument != parameter {
                // TODO: Specify which argument is incorrect.
                return error!(instruction_index, instruction);
            }
        }
        // Pop the object reference from the stack if this method is not static.
        if !is_static {
            try_pop_stack!(
                self,
                instruction_index,
                instruction,
                VerificationType::Object { .. }
            )?;
        }
        // Push the return type onto the stack, if applicable. Normally, this
        // is done by the called function, but here we need to simulate that.
        if let Some((return_type, is_wide_type)) = return_type {
            self.stack.push(return_type);
            // Add wide type padding, if necessary.
            if is_wide_type {
                self.stack.push(VerificationType::Top);
            }
        }
        // Continue.
        Ok(ControlFlowOutcome::Continue)
    }

    fn simulate_new(
        &mut self,
        instruction: &Instruction,
        instruction_index: u16,
        pool: &mut ConstantPool,
        class_index: u16,
    ) -> VerifyResult<ControlFlowOutcome> {
        // Verify that the class type exists.
        pool.try_get_class(class_index)?;
        // Push the class type onto the stack.
        self.stack.push(VerificationType::Object {
            cpool_index: class_index,
        });
        // Continue.
        Ok(ControlFlowOutcome::Continue)
    }

    fn simulate_new_array(
        &mut self,
        instruction: &Instruction,
        instruction_index: u16,
        pool: &mut ConstantPool,
        array_type: &ArrayType,
    ) -> VerifyResult<ControlFlowOutcome> {
        // Pop the initial array size from the stack.
        try_pop_stack!(
            self,
            instruction_index,
            instruction,
            VerificationType::Integer
        )?;
        // Push the array object reference onto the stack.
        self.stack.push(parse_array_type(pool, array_type)?);
        // Continue.
        Ok(ControlFlowOutcome::Continue)
    }

    fn simulate_new_array_reference(
        &mut self,
        instruction: &Instruction,
        instruction_index: u16,
        pool: &mut ConstantPool,
        class_index: u16,
        dimensions: u8,
    ) -> VerifyResult<ControlFlowOutcome> {
        // Pop the initial array sizes from the stack.
        for _ in 0..dimensions {
            try_pop_stack!(
                self,
                instruction_index,
                instruction,
                VerificationType::Integer
            )?;
        }
        // Push the array object reference onto the stack.
        self.stack.push(VerificationType::Object {
            cpool_index: class_index,
        });
        // Continue.
        Ok(ControlFlowOutcome::Continue)
    }

    fn simulate_array_length(
        &mut self,
        instruction: &Instruction,
        instruction_index: u16,
    ) -> VerifyResult<ControlFlowOutcome> {
        // Pop the array object reference from the stack.
        try_pop_stack!(
            self,
            instruction_index,
            instruction,
            VerificationType::Object { .. }
        )?;
        // Push the array length onto the stack.
        self.stack.push(VerificationType::Integer);
        // Continue.
        Ok(ControlFlowOutcome::Continue)
    }

    fn simulate_instanceof(
        &mut self,
        instruction: &Instruction,
        instruction_index: u16,
        pool: &ConstantPool,
        class_index: u16,
    ) -> VerifyResult<ControlFlowOutcome> {
        // Pop the object reference from the stack.
        try_pop_stack!(
            self,
            instruction_index,
            instruction,
            VerificationType::Object { .. }
        )?;
        // Verify that the given index points to a valid class.
        pool.try_get_class(class_index)?;
        // Push the result onto the stack.
        self.stack.push(VerificationType::Integer);
        // Continue.
        Ok(ControlFlowOutcome::Continue)
    }

    fn simulate_checkcast(
        &mut self,
        instruction: &Instruction,
        instruction_index: u16,
        pool: &ConstantPool,
        class_index: u16,
    ) -> VerifyResult<ControlFlowOutcome> {
        // Pop the object reference (or null) from the stack.
        let reference_type = try_pop_stack!(
            self,
            instruction_index,
            instruction,
            VerificationType::Object { .. } | VerificationType::Null
        )?;
        // Modify the stack depending on the reference type.
        match reference_type {
            // If the reference is a class, push the class
            // the reference should be casted to onto the stack.
            VerificationType::Object { .. } => {
                // Verify that the given index points to a valid class.
                pool.try_get_class(class_index)?;
                // Then push it onto the stack.
                self.stack.push(VerificationType::Object {
                    cpool_index: class_index,
                })
            }
            // If the reference is null, the stack is left unchanged.
            VerificationType::Null => self.stack.push(reference_type),
            _ => unreachable!(),
        }
        // Continue.
        Ok(ControlFlowOutcome::Continue)
    }

    fn simulate_monitor_operation(
        &mut self,
        instruction: &Instruction,
        instruction_index: u16,
    ) -> VerifyResult<ControlFlowOutcome> {
        // Pop the object reference from the stack.
        try_pop_stack!(
            self,
            instruction_index,
            instruction,
            VerificationType::Object { .. }
        )?;
        // Continue.
        Ok(ControlFlowOutcome::Continue)
    }

    fn simulate_throw(
        &mut self,
        instruction: &Instruction,
        instruction_index: u16,
    ) -> VerifyResult<ControlFlowOutcome> {
        // Pop the exception object from the stack.
        let throwable_object = try_pop_stack!(
            self,
            instruction_index,
            instruction,
            VerificationType::Object { .. }
        )?;
        // Clear the locals. The control flow graph should
        // recover these from the block's entry frame.
        self.locals.clear();
        // Clear the stack.
        self.stack.clear();
        // Push the exception back onto the stack.
        self.stack.push(throwable_object);
        // Throw the exception.
        Ok(ControlFlowOutcome::Throw)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use itertools::izip;

    macro_rules! initial_frame {
        (locals = [$($locals:expr),*], stack = [$($stack:expr),*] $(,)?) => {
            StackFrame {
                locals: vec![$($locals),*],
                stack: vec![$($stack),*],
            }
        };
    }

    macro_rules! assert_sim_eq {
        ($actual:ident, $expected:ident, $instruction_index:ident, $instruction:ident, $reason:literal) => {
            assert_eq!(
                $actual, $expected,
                "instruction simulation failed at instruction #{} ({}): {}",
                $instruction_index, $instruction, $reason
            );
        };
    }

    #[track_caller]
    fn test_simulation<const N: usize>(
        mut frame: StackFrame,
        instructions: [Instruction; N],
        locals: [&[VerificationType]; N],
        stack: [&[VerificationType]; N],
        results: [VerifyResult<ControlFlowOutcome>; N],
    ) {
        let mut pool = ConstantPool::default();
        let mut instruction_index = 0;
        for (instruction, expected_local, expected_stack, expected_result) in
            izip!(instructions, locals, stack, results)
        {
            let actual_result = StackFrame::simulate_execution(
                &mut frame,
                &mut pool,
                instruction_index,
                &instruction,
            );
            assert_sim_eq!(
                actual_result,
                expected_result,
                instruction_index,
                instruction,
                "control flow outcome mismatch"
            );

            let actual_locals = frame.locals();
            assert_sim_eq!(
                actual_locals,
                expected_local,
                instruction_index,
                instruction,
                "local variable mismatch"
            );

            let actual_stack = frame.stack();
            assert_sim_eq!(
                actual_stack,
                expected_stack,
                instruction_index,
                instruction,
                "stack frame mismatch"
            );

            instruction_index += 1;
        }
    }

    // TODO: Add more tests.

    #[test]
    fn test_store_operations() {
        test_simulation(
            initial_frame!(locals = [], stack = [],),
            [
                Instruction::Iconst_0,
                Instruction::Istore_0,
                Instruction::Lconst_0,
                Instruction::Lstore_1,
                Instruction::Dconst_0,
                Instruction::Dstore_3,
            ],
            [
                &[],
                &[VerificationType::Integer],
                &[VerificationType::Integer],
                &[
                    VerificationType::Integer,
                    VerificationType::Long,
                    VerificationType::Top,
                ],
                &[
                    VerificationType::Integer,
                    VerificationType::Long,
                    VerificationType::Top,
                ],
                &[
                    VerificationType::Integer,
                    VerificationType::Long,
                    VerificationType::Top,
                    VerificationType::Double,
                    VerificationType::Top,
                ],
            ],
            [
                &[VerificationType::Integer],
                &[],
                &[VerificationType::Long, VerificationType::Top],
                &[],
                &[VerificationType::Double, VerificationType::Top],
                &[],
            ],
            [
                Ok(ControlFlowOutcome::Continue),
                Ok(ControlFlowOutcome::Continue),
                Ok(ControlFlowOutcome::Continue),
                Ok(ControlFlowOutcome::Continue),
                Ok(ControlFlowOutcome::Continue),
                Ok(ControlFlowOutcome::Continue),
            ],
        );
    }
}
