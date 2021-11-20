use anyhow::{anyhow, bail, Result};

use crate::ast::LoxValue;

use crate::scanner::Token;
use std::collections::HashMap;

pub struct Environment {
    values: HashMap<String, LoxValue>,
    parent: Option<Box<Environment>>,
}

impl Environment {
    pub fn new() -> Box<Environment> {
        Box::new(Self {
            values: HashMap::new(),
            parent: None,
        })
    }

    pub fn create_inner(self: &mut Box<Self>) {
        let new = Box::new(Self {
            values: HashMap::new(),
            parent: None,
        });
        let parent = std::mem::replace(self, new);
        self.parent = Some(parent);
    }

    pub fn end_scope(self: &mut Box<Self>) {
        if let Some(parent) = self.parent.take() {
            let _ = std::mem::replace(self, parent);
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
