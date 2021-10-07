pub mod assembler;
pub mod disassembler;

mod mnemonic;
mod operand;
mod patterns;
mod tokens;

use crate::emu6510::addrmode::AddrMode;
use crate::emu6510::instruction::Instruction;
use crate::emu6510::mem64k::Ram64K;
use disassembler::Columns;
use std::io::Read;
use std::{collections::HashMap, fs::File, path::Path};

#[derive(Debug)]
pub enum AsmError {
    UndefinedSymbol(String),
    RedefinedSymbol(String, i32, i32),
    MissingOperand,
    NoOpCode(Instruction, AddrMode),
    SyntaxError(String),
    OriginTooLow(u16, u16),
    BranchTooFar(i32),
    InvalidMnemonic(String),
    ParseIntError(String, std::num::ParseIntError),
    AsmLineError(usize, Box<AsmError>),
    IoError(std::io::Error),
}

impl From<std::io::Error> for AsmError {
    fn from(err: std::io::Error) -> Self {
        Self::IoError(err)
    }
}

pub fn assemble_file<F: AsRef<Path>>(fname: F) -> Result<(u16, Vec<u8>, HashMap<String, i32>), AsmError> {
    let mut src = String::new();
    File::open(&fname)?.read_to_string(&mut src)?;
    let mut asm = assembler::Assembler::new();
    asm.process_file(false, &src)?;
    asm.process_file(true, &src)?;
    Ok((asm.origin(), asm.code().to_vec(), asm.symbols().clone()))
}

pub fn disassemble_file<F: AsRef<Path>>(start_addr: u16, end_addr: Option<u16>, fpath: F) -> Result<Vec<Columns>, AsmError> {
    let mut buf = Vec::new();
    let fsize = File::open(&fpath)?.read_to_end(&mut buf)?;
    let end_addr = end_addr.unwrap_or(start_addr.saturating_add(fsize as u16));
    let mut memory = Ram64K::new();
    memory.set_block(start_addr, &buf);
    let mut lc = start_addr;
    let mut lines = Vec::new();
    while lc < end_addr {
        lines.push(disassembler::disassemble(&memory, &mut lc));
    }
    Ok(lines)
}
