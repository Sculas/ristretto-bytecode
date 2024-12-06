use crate::{bytecode::*, errors::*};
use ristretto_classfile::{attributes::*, BaseType, ClassFile, FieldType, MethodAccessFlags};

macro_rules! find_attr {
    ($attrs:expr, $pattern:pat) => {
        $attrs.iter().find(|attr| matches!(attr, $pattern))
    };
}

#[derive(Clone, Debug, PartialEq)]
pub struct Method {
    // public fields that may be modified
    pub access_flags: MethodAccessFlags,
    pub name: String,
    pub descriptor: String,
    pub parameters: Vec<FieldType>,
    pub return_type: Option<FieldType>,
    pub instructions: Vec<Instruction>,
    pub try_catch_blocks: Vec<TryCatchBlock>,
    // private fields that are changed during compilation
    attributes: Vec<Attribute>,
    max_stack: usize,
    max_locals: usize,
}

impl Method {
    /// Create a new class method with the given definition.
    ///
    /// # Errors
    /// If the method name cannot be read.
    pub fn try_from(class: &ClassFile, definition: &ristretto_classfile::Method) -> Result<Self> {
        let constant_pool = &class.constant_pool;
        let name = constant_pool.try_get_utf8(definition.name_index)?;
        let descriptor = constant_pool.try_get_utf8(definition.descriptor_index)?;
        let (parameters, return_type) = Method::parse_descriptor(descriptor)?;

        let attributes = definition.attributes.clone();
        let (max_stack, max_locals, instructions, try_catch_blocks) =
            match find_attr!(attributes, Attribute::Code { .. }) {
                Some(Attribute::Code {
                    max_stack,
                    max_locals,
                    code,
                    exception_table,
                    // attributes, // TODO
                    ..
                }) => (
                    usize::from(*max_stack),
                    usize::from(*max_locals),
                    code.clone(),
                    exception_table.iter().cloned().map(Into::into).collect(),
                ),
                _ => Default::default(),
            };

        Ok(Method {
            // public fields
            access_flags: definition.access_flags,
            name: name.to_string(),
            descriptor: descriptor.to_string(),
            parameters,
            return_type,
            instructions,
            try_catch_blocks,
            // private fields,
            attributes,
            max_stack,
            max_locals,
        })
    }

    /// Compiles the [Method] into a [ristretto_classfile::Method].
    ///
    /// A [compilation mode][CompilationMode] must be specified to choose what should be recomputed or not.
    /// The [ClassFile] is required to make any changes to the [ConstantPool][ristretto_classfile::ConstantPool] if required.
    pub fn compile(
        &mut self,
        _class: &mut ClassFile,
        _compilation_mode: &CompilationMode,
    ) -> Result<ristretto_classfile::Method> {
        Err(Error::InvalidMethodDescriptor("TODO".into()))
    }

    /// Parse the method descriptor. The descriptor is a string representing the method signature.
    /// The descriptor has the following format:
    ///
    /// See: <https://docs.oracle.com/javase/specs/jvms/se23/html/jvms-4.html#jvms-4.3.3>
    ///
    /// # Errors
    /// If the descriptor cannot be parsed.
    pub fn parse_descriptor(descriptor: &str) -> Result<(Vec<FieldType>, Option<FieldType>)> {
        let mut chars = descriptor.chars().peekable();
        let mut parameters = Vec::new();
        let mut return_type = None;

        if chars.next() != Some('(') {
            return Err(Error::InvalidMethodDescriptor(descriptor.to_string()));
        }

        while let Some(&ch) = chars.peek() {
            if ch == ')' {
                chars.next();
                break;
            }
            parameters.push(Self::parse_field_type(descriptor, &mut chars)?);
        }

        match chars.next() {
            Some('V') => {}
            Some(ch) => {
                return_type = Some(Self::parse_field_type(
                    descriptor,
                    &mut std::iter::once(ch).chain(chars),
                )?);
            }
            None => return Err(Error::InvalidMethodDescriptor(descriptor.to_string())),
        }

        Ok((parameters, return_type))
    }

    /// Parse the field type.
    ///
    /// # Errors
    /// If the field type cannot be parsed.
    pub(crate) fn parse_field_type<I>(descriptor: &str, chars: &mut I) -> Result<FieldType>
    where
        I: Iterator<Item = char>,
    {
        match chars.next() {
            Some('L') => {
                let mut class_name = String::new();
                for ch in chars.by_ref() {
                    if ch == ';' {
                        break;
                    }
                    class_name.push(ch);
                }
                Ok(FieldType::Object(class_name))
            }
            Some('[') => {
                let component_type = Self::parse_field_type(descriptor, chars)?;
                Ok(FieldType::Array(Box::new(component_type)))
            }
            Some(value) => {
                let base_type = BaseType::parse(value)?;
                Ok(FieldType::Base(base_type))
            }
            None => Err(Error::InvalidMethodDescriptor(descriptor.to_string())),
        }
    }
}

impl std::fmt::Display for Method {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let parameters = self
            .parameters
            .iter()
            .map(std::string::ToString::to_string)
            .collect::<Vec<String>>()
            .join(", ");
        let return_type = match &self.return_type {
            Some(field_type) => field_type.to_string(),
            None => "void".to_string(),
        };
        write!(f, "{}({parameters}) -> {return_type}", self.name)
    }
}
