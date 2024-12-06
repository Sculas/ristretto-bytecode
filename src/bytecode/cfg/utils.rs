use crate::{Method, VerificationError, VerifyResult};
use ristretto_classfile::{
    attributes::{ArrayType, VerificationType},
    BaseType, Constant, ConstantPool, FieldType,
};

// TODO: Adding to the pool should be done by something else. We're a verifier after all!
// TODO: Remove index workarounds (pool.iter()) once it's fixed in ristretto_classfile.
// TODO: Add documentation and tests.

pub fn pool_get_or_add_utf8<S: AsRef<str>>(
    pool: &mut ConstantPool,
    value: S,
) -> ristretto_classfile::Result<u16> {
    let value = value.as_ref();

    let mut index = 0;
    for constant in pool.iter() {
        index += 1;
        match constant {
            Constant::Utf8(v) if v == value => {
                return Ok(index as u16);
            }
            Constant::Long(_) | Constant::Double(_) => index += 1,
            _ => {}
        }
    }

    pool.add_utf8(value)
}

pub fn pool_get_or_add_class<S: AsRef<str>>(
    pool: &mut ConstantPool,
    value: S,
) -> ristretto_classfile::Result<u16> {
    let value = value.as_ref();

    let mut index = 0;
    for constant in pool.iter() {
        index += 1;
        match constant {
            Constant::Class(utf8_index) => {
                if pool.try_get_utf8(*utf8_index).is_ok_and(|v| v == value) {
                    return Ok(index as u16);
                }
            }
            Constant::Long(_) | Constant::Double(_) => index += 1,
            _ => {}
        }
    }

    pool.add_class(value)
}

pub fn field_type_to_verification_type(
    pool: &mut ConstantPool,
    field_type: &FieldType,
) -> ristretto_classfile::Result<(VerificationType, bool)> {
    match field_type {
        FieldType::Array(field_type) => field_type_to_verification_type(pool, field_type),
        FieldType::Base(base_type) => Ok(match base_type {
            BaseType::Byte => (VerificationType::Integer, false),
            BaseType::Char => (VerificationType::Integer, false),
            BaseType::Int => (VerificationType::Integer, false),
            BaseType::Short => (VerificationType::Integer, false),
            BaseType::Boolean => (VerificationType::Integer, false),
            BaseType::Float => (VerificationType::Float, false),
            BaseType::Double => (VerificationType::Double, true),
            BaseType::Long => (VerificationType::Long, true),
        }),
        FieldType::Object(descriptor) => {
            let cpool_index = pool_get_or_add_class(pool, descriptor)?;
            Ok((VerificationType::Object { cpool_index }, false))
        }
    }
}

pub fn parse_array_type(
    pool: &mut ConstantPool,
    array_type: &ArrayType,
) -> VerifyResult<VerificationType> {
    Ok(VerificationType::Object {
        cpool_index: pool_get_or_add_class(
            pool,
            match array_type {
                ArrayType::Boolean | ArrayType::Byte => "[B",
                ArrayType::Char => "[C",
                ArrayType::Float => "[F",
                ArrayType::Double => "[D",
                ArrayType::Short => "[S",
                ArrayType::Int => "[I",
                ArrayType::Long => "[J",
            },
        )?,
    })
}

pub fn parse_array_reference(
    pool: &mut ConstantPool,
    verification_type: VerificationType,
) -> VerifyResult<(VerificationType, bool)> {
    let array_type = match verification_type {
        VerificationType::Object { cpool_index } => pool.try_get_class(cpool_index)?,
        _ => {
            return Err(VerificationError::InvalidFieldType(format!(
                "{verification_type}"
            )))
        }
    };
    let array_element_type = Method::parse_field_type("", &mut array_type.chars())
        .map_err(|_| VerificationError::InvalidFieldType(array_type.into()))?;
    match array_element_type {
        FieldType::Array(field_type) => Ok(field_type_to_verification_type(pool, &field_type)?),
        _ => Err(VerificationError::InvalidFieldType(array_type.into())),
    }
}

pub fn parse_field_reference(
    pool: &mut ConstantPool,
    field_index: u16,
) -> VerifyResult<(VerificationType, bool)> {
    // Retrieve the field descriptor from the constant pool.
    let (_, field_type_index) = pool.try_get_field_ref(field_index)?;
    let (_, field_descriptor_index) = pool.try_get_name_and_type(*field_type_index)?;
    let field_descriptor = pool.try_get_utf8(*field_descriptor_index)?;
    // Parse the field descriptor.
    let field_type = Method::parse_field_type("", &mut field_descriptor.chars())
        .map_err(|_| VerificationError::InvalidFieldType(field_descriptor.into()))?;
    // Return the field type as a verification type.
    Ok(field_type_to_verification_type(pool, &field_type)?)
}

#[allow(clippy::type_complexity)]
pub fn parse_method_reference(
    pool: &mut ConstantPool,
    is_callsite: bool,
    method_or_callsite_index: u16,
) -> VerifyResult<(Vec<VerificationType>, Option<(VerificationType, bool)>)> {
    // Retrieve the method type from the constant pool.
    let (_, method_type_index) = if is_callsite {
        pool.try_get_invoke_dynamic(method_or_callsite_index)?
    } else {
        pool.try_get_method_ref(method_or_callsite_index)?
    };
    // Retrieve the method descriptor from the constant pool.
    let (_, method_descriptor_index) = pool.try_get_name_and_type(*method_type_index)?;
    let method_descriptor = pool.try_get_utf8(*method_descriptor_index)?;
    // Parse the method descriptor.
    let (parameters, return_type) = Method::parse_descriptor(method_descriptor)
        .map_err(|_| VerificationError::InvalidMethodDescriptor(method_descriptor.into()))?;
    // Transform the field types into verification types.
    let parameters = parameters
        .into_iter()
        .map(|ty| field_type_to_verification_type(pool, &ty))
        .map(|ty| ty.map(|(ty, _)| ty))
        .collect::<ristretto_classfile::Result<Vec<_>>>()?;
    let return_type = return_type
        .map(|ty| field_type_to_verification_type(pool, &ty))
        .transpose()?;
    // Return the parameters and return type.
    Ok((parameters, return_type))
}

pub fn get_string_reference(pool: &mut ConstantPool) -> VerifyResult<VerificationType> {
    let string_type = FieldType::Object("java/lang/String".into());
    let (string_type, _) = field_type_to_verification_type(pool, &string_type)?;
    Ok(string_type)
}

pub fn is_wide_type(verification_type: &VerificationType) -> bool {
    matches!(
        verification_type,
        VerificationType::Double | VerificationType::Long | VerificationType::Top
    )
}

pub fn is_wide_type_invalid(value1: &VerificationType, value2: &VerificationType) -> bool {
    let value1_invalid = is_wide_type(value1) && !is_wide_type(value2);
    let value2_invalid = !is_wide_type(value1) && is_wide_type(value2);
    value1_invalid || value2_invalid
}
