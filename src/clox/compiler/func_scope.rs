use std::mem;

use anyhow::bail;

use crate::clox::mm::{HasRoots, ObjMarker};
use crate::clox::value::Function;

// This is struct Compiler in the book, Ch 22.
pub struct FunctionScope {
    pub(super) func_obj: Function,
    func_type: FunctionType,
    scope_depth: usize,
    locals: Vec<Local>,
    pub(super) upvalues: Vec<Upvalue>,
    enclosing: Option<Box<FunctionScope>>,
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Upvalue {
    Local(LocalIdx),
    Up(UpvalueIdx),
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub struct UpvalueIdx(u8);

impl From<UpvalueIdx> for u8 {
    fn from(value: UpvalueIdx) -> Self {
        value.0
    }
}

impl Upvalue {
    pub fn is_local(&self) -> bool {
        matches!(self, Self::Local(_))
    }

    pub fn index(&self) -> u8 {
        match self {
            Upvalue::Local(idx) => idx.0,
            Upvalue::Up(idx) => idx.0,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub struct LocalIdx(u8);

impl From<LocalIdx> for u8 {
    fn from(value: LocalIdx) -> Self {
        value.0
    }
}

pub enum ResolvedVariable {
    Local(LocalIdx),
    UpValue(UpvalueIdx),
}

impl From<LocalIdx> for ResolvedVariable {
    fn from(value: LocalIdx) -> Self {
        Self::Local(value)
    }
}

impl From<UpvalueIdx> for ResolvedVariable {
    fn from(value: UpvalueIdx) -> Self {
        Self::UpValue(value)
    }
}

impl FunctionScope {
    pub fn new(func_type: FunctionType) -> Box<Self> {
        let slot0_name = if func_type != FunctionType::Function {
            "this"
        } else {
            ""
        }
            .to_string();
        let this_slot = Local::new(slot0_name);
        let mut scope = Self {
            func_obj: Function::new(),
            func_type,
            scope_depth: 0,
            locals: vec![this_slot],
            upvalues: vec![],
            enclosing: None,
        };
        // mark the "this" slot as initialized
        scope.mark_local_initialized();
        scope.into()
    }

    pub fn function(&mut self) -> &mut Function {
        &mut self.func_obj
    }

    pub fn function_type(&self) -> FunctionType {
        self.func_type
    }

    pub fn is_global_scope(&self) -> bool {
        self.scope_depth == 0
    }

    pub fn begin_scope(&mut self) {
        self.scope_depth += 1;
    }

    pub fn end_scope(&mut self) -> impl Iterator<Item=bool> {
        self.scope_depth -= 1;
        let local_pos = self
            .locals
            .iter()
            .rposition(|local| local.depth() <= self.scope_depth);
        self.locals
            .split_off(local_pos.map(|p| p + 1).unwrap_or(0))
            .into_iter()
            .rev()
            .map(|local| local.is_captured())
    }

    pub fn make_inner_func_scope(self: &mut Box<Self>, func_type: FunctionType) {
        self.enclosing = Some(mem::replace(self, FunctionScope::new(func_type)));
        self.scope_depth = 1; // Only the root function scope is global
    }

    pub fn end_inner_func_scope(self: &mut Box<Self>) -> Box<Self> {
        let outer = self.enclosing.take().unwrap();
        mem::replace(self, outer)
    }

    pub fn add_local(&mut self, name: String) -> anyhow::Result<()> {
        if self.locals.len() > u8::MAX as usize {
            bail!("Too many local variables in function.");
        }
        self.locals.push(Local::new(name));
        Ok(())
    }

    /// Adds an upvalue to the upvalues array and returns the local index
    /// in the array. If the upvalue already exists the existing slot is returned.
    fn add_upvalue(&mut self, new: Upvalue) -> anyhow::Result<UpvalueIdx> {
        if let Some(i) = self.upvalues.iter().position(|&uv| uv == new) {
            return Ok(UpvalueIdx(i as u8));
        }
        if self.upvalues.len() >= 256 {
            bail!("Too many closure variables in function.")
        }
        self.upvalues.push(new);
        self.function().upvalue_count = self.upvalues.len();
        Ok(UpvalueIdx((self.function().upvalue_count - 1) as u8))
    }

    /// Check that the variable isn't already declared in the current scope
    pub fn declare_local(&mut self, name: String) -> anyhow::Result<()> {
        for local in self.locals.iter().rev() {
            if local.depth < self.scope_depth {
                break;
            }
            if local.name == name {
                bail!("Already a variable with this name in this scope.");
            }
        }
        self.add_local(name)
    }

    /// Find a named variable, either in the current stack frame or as an upvalue
    pub fn resolve_variable(&mut self, name: &str) -> anyhow::Result<Option<ResolvedVariable>> {
        if let Some(local) = self.resolve_local(name)? {
            Ok(Some(local.into()))
        } else {
            self.resolve_upvalue(name).map(|o| o.map(|o| o.into()))
        }
    }

    /// Returns the stack slot of a local variable, or None if no such local variable exists.
    /// Errors if the variable exists but isn't initialized.
    fn resolve_local(&self, name: &str) -> anyhow::Result<Option<LocalIdx>> {
        for (i, local) in self.locals.iter().enumerate().rev() {
            if local.name == name {
                if !local.is_initialized() {
                    bail!("Can't read local variable in its own initializer.");
                }
                return Ok(Some(LocalIdx(i as u8)));
            }
        }
        Ok(None)
    }

    /// Create a chain of upvalues through the function scopes,
    /// calling add_upvalue() in each scope and returning the result.
    fn resolve_upvalue(&mut self, name: &str) -> anyhow::Result<Option<UpvalueIdx>> {
        let Some(enclosing) = self.enclosing.as_mut() else {
            return Ok(None);
        };

        if let Some(local) = enclosing.resolve_local(name).unwrap() {
            // Mark the local variable as captured by an upvalue
            enclosing.locals[local.0 as usize].is_captured = true;
            Some(Upvalue::Local(local))
        } else {
            enclosing.resolve_upvalue(name)?.map(Upvalue::Up)
        }
            .map(|upvalue| self.add_upvalue(upvalue))
            .transpose()
    }

    /// Mark the newest local variable as initialized
    pub fn mark_local_initialized(&mut self) {
        self.locals
            .last_mut()
            .map(|local| local.depth = self.scope_depth);
    }
}

impl HasRoots for FunctionScope {
    fn mark_roots(&self, mark_obj: &mut ObjMarker) {
        self.func_obj.mark_roots(mark_obj);
        if let Some(e) = self.enclosing.as_ref() {
            e.mark_roots(mark_obj);
        }
    }
}

pub struct Local {
    name: String,
    depth: usize,
    is_captured: bool,
}

impl Local {
    pub fn new(name: String) -> Self {
        Self {
            name,
            depth: usize::MAX,
            is_captured: false,
        }
    }

    pub fn depth(&self) -> usize {
        self.depth
    }

    pub fn is_initialized(&self) -> bool {
        self.depth < usize::MAX
    }

    pub fn is_captured(&self) -> bool {
        self.is_captured
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum FunctionType {
    Function,
    Initializer,
    Method,
    Script,
}
