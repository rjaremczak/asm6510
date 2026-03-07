pub mod assembler;
pub mod disassembler;

mod addrmode;
mod instruction;
mod memory;
mod mnemonic;
mod operand;
mod operation;
mod patterns;
mod tokens;
pub(crate) mod error;

use addrmode::AddrMode;
use disassembler::Columns;
use instruction::Instruction;
use memory::Memory;
use std::io::Read;
use std::{collections::HashMap, fs::File, path::Path};

use crate::asm6510::error::AppError;

pub fn assemble_file<F: AsRef<Path>>(
    fname: F,
) -> Result<(u16, Vec<u8>, HashMap<String, i32>), AppError> {
    let mut src = String::new();
    File::open(&fname)?.read_to_string(&mut src)?;
    let mut asm = assembler::Assembler::new();
    asm.process_file(false, &src)?;
    asm.process_file(true, &src)?;
    Ok((asm.origin(), asm.code().to_vec(), asm.symbols().clone()))
}

pub fn disassemble_file<F: AsRef<Path>>(
    start_addr: u16,
    end_addr: Option<u16>,
    fpath: F,
) -> Result<Vec<Columns>, AppError> {
    let mut buf = Vec::new();
    let fsize = File::open(&fpath)?.read_to_end(&mut buf)?;
    let end_addr = end_addr.unwrap_or(start_addr.saturating_add(fsize as u16));
    let mut memory = Memory::new();
    memory.set_block(start_addr, &buf);
    let mut lc = start_addr;
    let mut lines = Vec::new();
    while lc < end_addr {
        lines.push(disassembler::disassemble(&memory, &mut lc));
    }
    Ok(lines)
}
