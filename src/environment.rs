use anyhow::{anyhow, bail, Result};

use crate::scanner::Token;
use crate::LoxType;

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

pub type Env = Rc<Environment>;

pub struct Environment {
    values: RefCell<HashMap<String, LoxType>>,
    parent: Option<Env>,
}

impl Environment {
    pub fn new() -> Env {
        Rc::new(Environment {
            values: HashMap::new().into(),
            parent: None,
        })
    }

    pub fn create_local(self: &Env) -> Env {
        let mut new = Self::new();
        Rc::get_mut(&mut new).unwrap().parent = Some(Rc::clone(self));
        new
    }

    pub fn assign(&self, name: &Token, value: LoxType) -> Result<()> {
        if let Some(val) = self.values.borrow_mut().get_mut(name.lexeme()) {
            *val = value;
            Ok(())
        } else if let Some(parent) = &self.parent {
            parent.assign(name, value)
        } else {
            bail!("Undefined variable '{}'.", name.lexeme());
        }
    }

    pub fn define(&self, name: &str, value: LoxType) {
        self.values.borrow_mut().insert(name.to_owned(), value);
    }

    pub fn get(&self, name: &Token) -> Result<LoxType> {
        // FIXME: Use Cow values
        if let Some(val) = self.values.borrow().get(name.lexeme()) {
            Ok(val.clone())
        } else if let Some(parent) = &self.parent {
            parent.get(name)
        } else {
            Err(anyhow!("Undefined variable '{}' ", name.lexeme()))
        }
    }
}
