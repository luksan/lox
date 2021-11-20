use anyhow::{anyhow, bail, Result};

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

    pub fn assign(&mut self, name: &Token, value: LoxValue) -> Result<()> {
        if let Some(val) = self.values.get_mut(name.lexeme()) {
            *val = value;
            Ok(())
        } else if let Some(parent) = &mut self.parent {
            parent.assign(name, value)
        } else {
            bail!("Undefined variable '{}'.", name.lexeme());
        }
    }

    pub fn define(&mut self, name: &str, value: LoxValue) {
        self.values.insert(name.to_owned(), value);
    }

    pub fn get(&self, name: &Token) -> Result<LoxValue> {
        // FIXME: Use Cow values
        if let Some(val) = self.values.get(name.lexeme()) {
            Ok(val.clone())
        } else if let Some(parent) = &self.parent {
            parent.get(name)
        } else {
            Err(anyhow!("Undefined variable '{}' ", name.lexeme()))
        }
    }
}
