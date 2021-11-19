use anyhow::{anyhow, Result};

use crate::ast::LoxValue;

use crate::scanner::Token;
use std::collections::HashMap;

pub struct Environment<'parent> {
    values: HashMap<String, LoxValue>,
    parent: Option<&'parent mut Environment<'parent>>,
}

impl Environment<'_> {
    pub fn new() -> Environment<'static> {
        Environment {
            values: HashMap::new(),
            parent: None,
        }
    }

    pub fn define(&mut self, name: &str, value: LoxValue) {
        self.values.insert(name.to_owned(), value);
    }

    pub fn get(&self, name: &Token) -> Result<LoxValue> {
        // FIXME: Use Cow values
        Ok(self
            .values
            .get(name.lexeme())
            .ok_or_else(|| anyhow!("Undefined variable '{}' ", name.lexeme()))?
            .clone())
    }
}
