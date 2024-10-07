use anyhow::{anyhow, bail, Result};

use crate::jlox::LoxType;
use crate::scanner::Token;

use std::cell::RefCell;
use std::collections::HashMap;
use std::ops::Deref;
use std::rc::Rc;

#[derive(Clone, Debug)]
pub struct Env {
    env: Rc<Environment>,
}

impl Env {
    pub fn new() -> Self {
        Self {
            env: Rc::new(Environment::default()),
        }
    }

    pub fn create_local(&self) -> Self {
        Self {
            env: Rc::new(Environment::create_inner_env(self.clone())),
        }
    }
}

// Drop impl to clear circular references caused by closures
impl Drop for Env {
    fn drop(&mut self) {
        let sc = Rc::strong_count(&self.env);
        if sc < 2 {
            return;
        }
        let hashmap = match self.env.values.try_borrow() {
            Ok(v) => v,
            Err(_) => return, // Drop already running
        };

        if sc - 1 > hashmap.len() {
            return; // there can't be enough circular references to drop the count to zero
        }
        let mut circ_ref_cnt = 0;
        for val in hashmap.values() {
            match val {
                LoxType::Class(cls) => {
                    for fun in cls.methods.values() {
                        if fun.closure == *self {
                            circ_ref_cnt += 1;
                        }
                    }
                }
                LoxType::Function(fun) => {
                    if fun.closure == *self {
                        circ_ref_cnt += 1;
                    }
                }
                _ => {}
            }
        }
        std::mem::drop(hashmap);
        if sc - 1 <= circ_ref_cnt {
            // only circular references left. Purge the hashmap
            self.env.values.borrow_mut().clear();
            assert_eq!(Rc::strong_count(&self.env), 1);
        }
    }
}

impl Deref for Env {
    type Target = Environment;

    fn deref(&self) -> &Self::Target {
        &self.env
    }
}

impl PartialEq for Env {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.env, &other.env)
    }
}

#[derive(Debug, Default)]
pub struct Environment {
    values: RefCell<HashMap<String, LoxType>>,
    parent: Option<Env>,
}

impl Environment {
    fn create_inner_env(parent: Env) -> Self {
        Self {
            parent: Some(parent),
            ..Self::default()
        }
    }

    fn ancestor(&self, distance: usize) -> &Environment {
        if distance > 0 {
            self.parent.as_ref().unwrap().ancestor(distance - 1)
        } else {
            self
        }
    }

    pub fn assign(&self, name: &Token, value: LoxType) -> Result<()> {
        if let Some(val) = self.values.borrow_mut().get_mut(name.lexeme()) {
            *val = value;
            Ok(())
        } else if let Some(parent) = &self.parent {
            parent.assign(name, value)
        } else {
            bail!(
                "Undefined variable '{}'.\n[line {}]",
                name.lexeme(),
                name.line()
            );
        }
    }

    pub fn define(&self, name: &str, value: LoxType) {
        self.values.borrow_mut().insert(name.to_owned(), value);
    }

    pub fn get(&self, name: &Token) -> Result<LoxType> {
        if let Some(val) = self.values.borrow().get(name.lexeme()) {
            Ok(val.clone())
        } else if let Some(parent) = &self.parent {
            parent.get(name)
        } else {
            Err(anyhow!(
                "Undefined variable '{}'.\n[line {}]",
                name.lexeme(),
                name.line()
            ))
        }
    }

    pub fn assign_at(&self, distance: usize, name: &Token, value: LoxType) -> Result<()> {
        self.ancestor(distance)
            .values
            .borrow_mut()
            .insert(name.lexeme().to_string(), value);
        Ok(())
    }

    /// Get a variable at a certain environment depth.
    /// If this returns None there is a bug in the Lox implementation,
    /// probably in the resolver pass or the garbage collection.
    pub fn get_at(&self, name: &str, depth: usize) -> Option<LoxType> {
        self.ancestor(depth)
            .values
            .borrow_mut()
            .get(name)
            .cloned()
    }
}
