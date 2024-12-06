use crate::{errors::*, Method};
use ristretto_classfile::ClassFile;

pub mod cfg;
mod mode;
mod try_catch_block;

pub use mode::*;
pub use try_catch_block::*;

pub trait Bytecode {
    fn method(&self, name_descriptor: (&str, &str)) -> Result<Method>;
}

impl Bytecode for ClassFile {
    fn method(&self, (name, descriptor): (&str, &str)) -> Result<Method> {
        for method in &self.methods {
            let method_name = self.constant_pool.try_get_utf8(method.name_index)?;
            let method_descriptor = self.constant_pool.try_get_utf8(method.descriptor_index)?;
            if method_name == name && method_descriptor == descriptor {
                return Method::try_from(self, method);
            }
        }

        Err(Error::NoSuchMethod(format!("{name}{descriptor}")))
    }
}
