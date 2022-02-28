mod compiler;
mod mm;
mod table;
mod value;
mod vm;

use mm::ValueArray;
use value::{Function, Value};
pub use vm::{Vm, VmError};

use num_enum::FromPrimitive;
use once_cell::sync::OnceCell;

use std::fmt::{Debug, Formatter};

#[derive(Default, Debug, Copy, Clone)]
pub struct CloxSettings {
    pub output_ci_compliant: bool,
    pub trace_execution: bool,
    pub disassemble_compiler_output: bool,
    pub gc_stress_test: bool,
}

static SETTINGS: OnceCell<CloxSettings> = OnceCell::new();

pub fn set_settings(settings: CloxSettings) {
    SETTINGS
        .set(settings)
        .expect("Can't set settings more than once.");
}

fn get_settings() -> CloxSettings {
    SETTINGS.get().copied().unwrap_or(CloxSettings::default())
}

#[derive(Copy, Clone, Debug, FromPrimitive)]
#[repr(u8)]
enum OpCode {
    Constant,
    Nil,
    True,
    False,
    GetUpvalue,
    SetUpvalue,
    GetProperty,
    SetProperty,
    Equal,
    Pop,
    GetLocal,
    SetLocal,
    GetGlobal,
    DefineGlobal,
    SetGlobal,
    Greater,
    Less,
    Add,
    Subtract,
    Multiply,
    Divide,
    Not,
    Negate,
    Print,
    Jump,
    JumpIfFalse,
    Loop,
    Call,
    Closure,
    CloseUpvalue,
    Return,
    Class,
    #[num_enum(default)]
    BadOpCode,
}

impl Into<u8> for OpCode {
    fn into(self) -> u8 {
        self as u8
    }
}

pub struct Chunk {
    code: Vec<u8>,
    constants: ValueArray,
    lines: Vec<u16>,
}

impl Chunk {
    pub fn new() -> Self {
        Self {
            code: Vec::with_capacity(0),
            constants: ValueArray::new(),
            lines: vec![],
        }
    }

    pub fn add_constant(&mut self, val: impl Into<Value>) -> usize {
        self.constants.write(val.into())
    }

    pub fn write_u8(&mut self, byte: impl Into<u8>, line: u16) {
        self.code.push(byte.into());
        self.lines.push(line);
    }

    pub fn disassemble(&self, name: &str) {
        println!("== {} ==", name);
        let mut offset = 0;
        while offset < self.code.len() {
            offset = self.disassemble_instruction(offset);
        }
    }

    fn disassemble_instruction(&self, offset: usize) -> usize {
        print!("{:04} ", offset);
        if offset > 0 && self.lines[offset] == self.lines[offset - 1] {
            print!("   | ");
        } else {
            print!("{:4} ", self.lines[offset]);
        }

        let instr = self.code[offset];
        let op: OpCode = instr.into();
        let op_str = format!("{:?}", op);

        let simple_instr = || {
            println!("{:12}", op_str);
            offset + 1
        };
        let constant_instr = || {
            let c = self.code[offset + 1];
            println!("{:12} {:3} {:?}", op_str, c, self.constants[c]);
            offset + 2
        };
        let byte_instr = || {
            let slot = self.code[offset + 1];
            println!("{:12} {:3}", op_str, slot);
            offset + 2
        };
        let jump_instr = |sign| {
            let jump = (self.code[offset + 1] as isize) << 8 | self.code[offset + 2] as isize;
            println!(
                "{:12} {:3} -> {}",
                op_str,
                offset,
                offset as isize + 3 + sign * jump
            );
            offset + 3
        };
        match op {
            OpCode::Constant => constant_instr(),
            OpCode::Nil => simple_instr(),
            OpCode::True => simple_instr(),
            OpCode::False => simple_instr(),
            OpCode::GetLocal => byte_instr(),
            OpCode::SetLocal => byte_instr(),
            OpCode::GetGlobal => constant_instr(),
            OpCode::DefineGlobal => constant_instr(),
            OpCode::SetGlobal => constant_instr(),
            OpCode::GetUpvalue => byte_instr(),
            OpCode::SetUpvalue => byte_instr(),
            OpCode::GetProperty => constant_instr(),
            OpCode::SetProperty => constant_instr(),
            OpCode::Equal => simple_instr(),
            OpCode::Pop => simple_instr(),
            OpCode::Greater => simple_instr(),
            OpCode::Less => simple_instr(),
            OpCode::Add => simple_instr(),
            OpCode::Subtract => simple_instr(),
            OpCode::Multiply => simple_instr(),
            OpCode::Divide => simple_instr(),
            OpCode::Not => simple_instr(),
            OpCode::Negate => simple_instr(),
            OpCode::Print => simple_instr(),
            OpCode::Jump => jump_instr(1),
            OpCode::JumpIfFalse => jump_instr(1),
            OpCode::Loop => jump_instr(-1),
            OpCode::Call => byte_instr(),
            OpCode::Closure => {
                let mut offset = offset + 1;
                let constant = self.code[offset];
                offset += 1;
                print!("{:12}{:4} ", op_str, constant);
                print!("{}", self.constants[constant]);
                println!();

                let function = self.constants[constant].as_object::<Function>().expect(
                    format!(
                        "Closure without function, found {:?}",
                        self.constants[constant]
                    )
                    .as_str(),
                );
                for _ in 0..function.upvalue_count {
                    let is_local = if self.code[offset] == 1 {
                        "local"
                    } else {
                        "upvalue"
                    };
                    let index = self.code[offset + 1];
                    offset += 2;
                    println!("{:04}    | {:<14} {}", offset - 2, is_local, index);
                }
                offset
            }
            OpCode::CloseUpvalue => simple_instr(),
            OpCode::Return => simple_instr(),
            OpCode::Class => constant_instr(),

            OpCode::BadOpCode => {
                println!("Unknown opcode {}", instr);
                offset + 1
            }
        }
    }
}

impl Debug for Chunk {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "<chunk {:?}>", self as *const _)
    }
}
