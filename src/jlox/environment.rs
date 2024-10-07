use anyhow::{anyhow, bail, Result};

use crate::jlox::LoxType;
use crate::scanner::Token;

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};
use std::ops::Deref;
use std::rc::{Rc, Weak};

#[derive(Clone)]
pub struct Env {
    env: Rc<Environment>,
    gc: Rc<EnvGcTracker>,
}

impl Debug for Env {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.env.fmt(f)
    }
}

#[derive(Debug)]
struct EnvGcTracker {
    envs: RefCell<Vec<Weak<Environment>>>,
}

impl EnvGcTracker {
    fn new_env(&self, parent: Option<Env>) -> Rc<Environment> {
        let env = if let Some(p) = parent {
            Rc::new(Environment::create_inner_env(p))
        } else {
            Rc::new(Environment::default())
        };
        self.envs.borrow_mut().push(Rc::downgrade(&env));
        env
    }

    fn run_gc(&self) {
        let mut to_trace = vec![];
        {
            let envs = self.envs.borrow_mut();
            for e in envs.iter().filter_map(|w| w.upgrade()) {
                if e.pinned.get() {
                    to_trace.push(e);
                }
            }
        }
        while let Some(env) = to_trace.pop() {
            if env.reachable.get() {
                continue;
            }
            env.reachable.set(true);

            if let Some(parent) = env.parent.as_ref() {
                to_trace.push(parent.env.clone());
            }

            let mut cb = |env: &Env| { if !env.reachable.get() { to_trace.push(env.env.clone()) } };
            for v in env.values.borrow().values() {
                v.env_gc_trace(&mut cb);
            }
        }

        let mut envs = self.envs.borrow_mut();

        /*
        println!("Env trace complete.");
        for e in envs.iter().filter_map(|w| w.upgrade()) {
            println!("Pre purge GC: {e:?}")
        }
        println!("=====");
         */

        envs.retain(|env| {
            if let Some(env) = env.upgrade() {
                if env.reachable.get() {
                    env.reachable.set(false); // reset for next GC run
                    return true;
                }
                env.purge_values() // break reference cycles
            }
            false
        })
    }
}

impl Env {
    pub fn new_root_env() -> Env {
        let gc = Rc::new(EnvGcTracker { envs: RefCell::new(Vec::new()) });
        Env {
            env: gc.new_env(None),
            gc,
        }
    }

    pub fn create_local(&self) -> Self {
        Self {
            env: self.gc.new_env(Some(self.clone())),
            gc: self.gc.clone(),
        }
    }

    pub fn new_orphan(&self) -> Self {
        Self {
            env: self.gc.new_env(None),
            gc: self.gc.clone(),
        }
    }

    pub fn run_gc(&self) {
        self.gc.run_gc();
    }
}

pub struct RootedEnv(Env);

impl Deref for RootedEnv {
    type Target = Env;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl RootedEnv {
    pub fn new(env: Env) -> Self {
        env.pinned.set(true);
        Self(env)
    }
}

impl Drop for RootedEnv {
    fn drop(&mut self) {
        self.0.pinned.set(false);
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

#[derive(Default)]
pub struct Environment {
    values: RefCell<HashMap<String, LoxType>>,
    parent: Option<Env>,
    reachable: Cell<bool>,
    pinned: Cell<bool>, // considered as GC root
}

impl Debug for Environment {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Environment {{ {self:p}, reachable {:?}, pinned {:?} }}", self.reachable.get(), self.pinned.get())?;
        if f.alternate() { return Ok(()); }

        // TODO print parent ref
        for (k, v) in self.values.borrow().iter() {
            writeln!(f, " {k}: {v:?}")?;
        }
        Ok(())
    }
}

impl Environment {
    fn create_inner_env(parent: Env) -> Self {
        Self {
            parent: Some(parent),
            ..Self::default()
        }
    }

    fn purge_values(&self) {
        let mut x = self.values.borrow_mut();
        // println!("Purging env {:p}", self);
        x.clear();
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
