mod compiler;
mod mm;
mod table;
mod value;
mod vm;

pub use vm::Vm;

use num_enum::FromPrimitive;

use mm::{Heap, ValueArray};
use value::Value;

use std::fmt::Debug;

#[derive(Copy, Clone, Debug, FromPrimitive)]
#[repr(u8)]
enum OpCode {
    Constant,
    Nil,
    True,
    False,
    Equal,
    Greater,
    Less,
    Add,
    Subtract,
    Multiply,
    Divide,
    Not,
    Negate,
    Return,
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
    const_heap: Heap,
    lines: Vec<u16>,
}

impl Chunk {
    pub fn new() -> Self {
        Self {
            code: Vec::with_capacity(0),
            constants: ValueArray::new(),
            const_heap: Heap::new(),
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

        let simple_instr = || {
            println!("{:?}", op);
            offset + 1
        };
        let constant_instr = || {
            let c = self.code[offset + 1];
            // FIXME: debug fmt alignment not working
            println!("{:16?} {:4} {:?}", op, c, self.constants[c]);
            offset + 2
        };
        match op {
            OpCode::Constant => constant_instr(),
            OpCode::Nil => simple_instr(),
            OpCode::True => simple_instr(),
            OpCode::False => simple_instr(),
            OpCode::Equal => simple_instr(),
            OpCode::Greater => simple_instr(),
            OpCode::Less => simple_instr(),
            OpCode::Add => simple_instr(),
            OpCode::Subtract => simple_instr(),
            OpCode::Multiply => simple_instr(),
            OpCode::Divide => simple_instr(),
            OpCode::Not => simple_instr(),
            OpCode::Negate => simple_instr(),
            OpCode::Return => simple_instr(),

            OpCode::BadOpCode => {
                println!("Unknown opcode {}", instr);
                offset + 1
            }
        }
    }
}
