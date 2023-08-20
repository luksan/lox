use anyhow::{anyhow, bail, Context, Result};

use crate::jlox::LoxType;
use crate::scanner::Token;

use std::cell::RefCell;
use std::collections::HashMap;
use std::ops::Deref;
use std::rc::Rc;

#[derive(Clone, Debug)]
pub struct Env(Rc<Environment>);

impl Env {
    pub fn new(env: Environment) -> Self {
        Self(Rc::new(env))
    }

    pub fn create_local(&self) -> Self {
        Environment::new(Some(self.clone()))
    }
}

// Drop impl to clear circular references caused by closures
impl Drop for Env {
    fn drop(&mut self) {
        let sc = Rc::strong_count(&self.0);
        if sc < 2 {
            return;
        }
        let hashmap = match self.0.values.try_borrow() {
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
            self.0.values.borrow_mut().clear();
            assert_eq!(Rc::strong_count(&self.0), 1);
        }
    }
}

impl Deref for Env {
    type Target = Environment;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl PartialEq for Env {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

#[derive(Debug)]
pub struct Environment {
    values: RefCell<HashMap<String, LoxType>>,
    parent: Option<Env>,
}

impl Environment {
    #[allow(clippy::new_ret_no_self)]
    pub fn new(parent: Option<Env>) -> Env {
        Env::new(Environment {
            values: HashMap::new().into(),
            parent,
        })
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

    pub fn get_at(&self, name: &str, depth: usize) -> Result<LoxType> {
        self.ancestor(depth)
            .values
            .borrow_mut()
            .get(name)
            .cloned()
            .with_context(|| format!("Resolver failure! Undefined variable '{}'.", name))
    }
}
