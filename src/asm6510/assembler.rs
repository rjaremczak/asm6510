use crate::asm6510::patterns;
use crate::emu6510::{addrmode::*, instruction::*, *};

use super::operand::{Operand, Resolver};
use super::tokens::Tokens;
use super::AsmError;

use regex::Regex;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::str::FromStr;
use AddrMode::Implied;
use Instruction::{JMP, JSR};

type Handler = fn(&mut Assembler, tokens: Tokens) -> Result<(), AsmError>;

const DEFAULT_LOCATION_COUNTER: u16 = 0;

pub struct Assembler {
    handlers: Vec<(Regex, Handler)>,
    resolver: Resolver,
    origin: Option<u16>,
    code: Vec<u8>,
    generate_code: bool,
    location_counter: u16,
    op_list_separator: Regex,
}

impl Assembler {
    pub fn new() -> Assembler {
        Assembler {
            code: Vec::new(),
            origin: None,
            location_counter: 0,
            generate_code: false,
            resolver: Resolver::new(),
            op_list_separator: Regex::new("(?:\\s*,\\s*)|(?:\\s+)").unwrap(),
            handlers: {
                let p = patterns::AsmPatterns::new();
                vec![
                    (p.empty_line, Assembler::handle_empty_line),
                    (p.cmd_set_location_counter, Assembler::handle_set_location_counter),
                    (p.cmd_emit_bytes, Assembler::handle_emit_bytes),
                    (p.cmd_emit_words, Assembler::handle_emit_words),
                    (p.ins_implied, Assembler::handle_implied),
                    (p.ins_immediate, Assembler::handle_immediate),
                    (p.ins_branch, Assembler::handle_relative),
                    (p.ins_absolute, Assembler::handle_absolute),
                    (p.ins_absolute_indexed_x, Assembler::handle_absolute_indexed_x),
                    (p.ins_absolute_indexed_y, Assembler::handle_absolute_indexed_y),
                    (p.ins_indirect, Assembler::handle_indirect),
                    (p.ins_indexed_indirect_x, Assembler::handle_indexed_indirect_x),
                    (p.ins_indirect_indexed_y, Assembler::handle_indirect_indexed_y),
                ]
            },
        }
    }

    pub fn process_line(&mut self, line: &str) -> Result<(), AsmError> {
        for (regex, handler) in self.handlers.iter() {
            if let Some(captures) = regex.captures(&line) {
                let tokens = Tokens::new(captures);
                if let Some(label) = tokens.label() {
                    self.resolver.define_symbol(label, self.location_counter as i32)?;
                };
                return handler(self, tokens);
            }
        }
        Err(AsmError::SyntaxError(String::from(line)))
    }

    fn parse_operand_list(&self, oplist: Option<&str>) -> Result<Vec<i32>, AsmError> {
        match oplist {
            Some(oplist) => {
                let mut values: Vec<i32> = Vec::new();
                for opstr in self.op_list_separator.split(oplist) {
                    match self.resolver.resolve(opstr, self.generate_code) {
                        Ok(operand) => values.push(operand.value),
                        Err(err) => return Err(err),
                    }
                }
                Ok(values)
            }
            None => Err(AsmError::MissingOperand),
        }
    }

    fn prepare_operand(&mut self, addrmode: AddrMode, opstr: Option<&str>) -> Result<Operand, AsmError> {
        if addrmode == AddrMode::Implied {
            Ok(Operand::literal(0))
        } else {
            let opstr = opstr.ok_or(AsmError::MissingOperand)?;
            let mut operand = self.resolver.resolve(opstr, self.generate_code)?;
            if self.generate_code && addrmode == AddrMode::Relative && operand.symbolic {
                let diff = operand.value - self.location_counter as i32 - 2;
                let displacement = i8::try_from(diff).map_err(|_| AsmError::BranchTooFar(diff))?;
                operand.value = displacement as i32;
            }
            Ok(operand)
        }
    }

    fn assemble(&mut self, addrmode: AddrMode, tokens: Tokens) -> Result<(), AsmError> {
        let operand = self.prepare_operand(addrmode, tokens.operand())?;
        let mnemonic = tokens.operation().ok_or(AsmError::SyntaxError(tokens.to_string()))?;
        let instruction = Instruction::from_str(mnemonic)?;
        let addrmode = optimize_addrmode(instruction, addrmode, operand);
        let opcode = operation::find_opcode(instruction, addrmode).ok_or(AsmError::NoOpCode(instruction, addrmode))?;
        self.emit_byte(opcode);
        match addrmode.len() {
            1 => self.emit_byte(operand.value as u8),
            2 => self.emit_word(operand.value as u16),
            _ => {}
        }
        Ok(())
    }

    pub fn init_pass(&mut self, generate_code: bool) {
        self.generate_code = generate_code;
        self.origin = None;
        self.location_counter = DEFAULT_LOCATION_COUNTER;
        self.code.clear();
    }

    pub fn code(&self) -> &Vec<u8> {
        &self.code
    }

    pub fn symbols(&self) -> &HashMap<String, i32> {
        self.resolver.symbols()
    }

    pub fn origin(&self) -> u16 {
        self.origin.unwrap_or(self.location_counter)
    }

    fn handle_empty_line(&mut self, _: Tokens) -> Result<(), AsmError> {
        Ok(())
    }

    fn handle_set_location_counter(&mut self, tokens: Tokens) -> Result<(), AsmError> {
        let str = tokens.operand().ok_or(AsmError::MissingOperand)?;
        let operand = self.resolver.resolve(str, false)?;
        self.set_location_counter(operand.value as u16)
    }

    fn handle_emit_bytes(&mut self, tokens: Tokens) -> Result<(), AsmError> {
        let values = self.parse_operand_list(tokens.operand())?;
        values.iter().for_each(|v| self.emit_byte(*v as u8));
        Ok(())
    }

    fn handle_emit_words(&mut self, tokens: Tokens) -> Result<(), AsmError> {
        let values = self.parse_operand_list(tokens.operand())?;
        values.iter().for_each(|v| self.emit_word(*v as u16));
        Ok(())
    }

    fn handle_implied(&mut self, tokens: Tokens) -> Result<(), AsmError> {
        self.assemble(AddrMode::Implied, tokens)
    }

    fn handle_immediate(&mut self, tokens: Tokens) -> Result<(), AsmError> {
        self.assemble(AddrMode::Immediate, tokens)
    }

    fn handle_relative(&mut self, tokens: Tokens) -> Result<(), AsmError> {
        self.assemble(AddrMode::Relative, tokens)
    }

    fn handle_absolute(&mut self, tokens: Tokens) -> Result<(), AsmError> {
        self.assemble(AddrMode::Absolute, tokens)
    }

    fn handle_absolute_indexed_x(&mut self, tokens: Tokens) -> Result<(), AsmError> {
        self.assemble(AddrMode::IndexedX, tokens)
    }

    fn handle_absolute_indexed_y(&mut self, tokens: Tokens) -> Result<(), AsmError> {
        self.assemble(AddrMode::IndexedY, tokens)
    }

    fn handle_indirect(&mut self, tokens: Tokens) -> Result<(), AsmError> {
        self.assemble(AddrMode::Indirect, tokens)
    }

    fn handle_indexed_indirect_x(&mut self, tokens: Tokens) -> Result<(), AsmError> {
        self.assemble(AddrMode::IndexedIndirectX, tokens)
    }

    fn handle_indirect_indexed_y(&mut self, tokens: Tokens) -> Result<(), AsmError> {
        self.assemble(AddrMode::IndirectIndexedY, tokens)
    }

    fn emit_byte(&mut self, byte: u8) {
        if self.generate_code {
            self.code.push(byte);
        }
        self.location_counter = self.location_counter.wrapping_add(1);
    }

    fn emit_word(&mut self, word: u16) {
        self.emit_byte(word as u8);
        self.emit_byte((word >> 8) as u8);
    }

    pub fn set_location_counter(&mut self, addr: u16) -> Result<(), AsmError> {
        if self.origin.is_none() {
            self.origin = Some(addr);
            self.location_counter = addr;
            Ok(())
        } else if addr >= self.location_counter {
            let lc = self.location_counter;
            self.location_counter = addr;
            if self.generate_code {
                for _ in lc..self.location_counter {
                    self.code.push(0)
                }
            }
            Ok(())
        } else {
            Err(AsmError::OriginTooLow(addr, self.location_counter))
        }
    }

    pub fn process_file(&mut self, generate_code: bool, strbuf: &String) -> Result<(), AsmError> {
        self.init_pass(generate_code);
        for (num, line) in strbuf.lines().enumerate() {
            self.process_line(line).map_err(|e| AsmError::AsmLineError(num + 1, Box::from(e)))?;
        }
        Ok(())
    }
}

fn optimize_addrmode(instr: Instruction, addrmode: AddrMode, op: Operand) -> AddrMode {
    if addrmode != Implied && instr != JSR && instr != JMP && !op.symbolic && op.value >= 0 && op.value <= 255 {
        match addrmode {
            AddrMode::Absolute => AddrMode::ZeroPage,
            AddrMode::IndexedX => AddrMode::ZeroPageX,
            AddrMode::IndexedY => AddrMode::ZeroPageY,
            _ => addrmode,
        }
    } else {
        addrmode
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_next(asm: &mut Assembler, line: &str, expected: &[u8]) {
        let r = asm.process_line(line);
        assert!(r.is_ok(), "line \"{}\" : {:?}", line, r);
        assert!(asm.code.len() >= expected.len(), "line \"{}\" : code too short", line);
        let generated = &asm.code[(asm.code.len() - expected.len())..];
        assert_eq!(generated, expected, "generated code {:?} differs from {:?}", generated, expected);
    }

    fn assert_asm(line: &str, code: &[u8]) -> Assembler {
        let mut asm = Assembler::new();
        asm.init_pass(true);
        assert_next(&mut asm, line, code);
        asm
    }

    #[test]
    fn init() {
        let asm = Assembler::new();
        assert_eq!(asm.generate_code, false);
        assert_eq!(asm.location_counter, 0);
        assert_eq!(asm.resolver.symbols().len(), 0);
    }

    #[test]
    fn tokenize() {
        let patterns = patterns::AsmPatterns::new();
        let captures = patterns.ins_absolute_indexed_x.captures("LDA etykieta,X").unwrap();
        let tokens = Tokens::new(captures);
        assert_eq!(tokens.operation(), Some("LDA"));
        assert_eq!(tokens.operand(), Some("etykieta"));
    }

    #[test]
    fn list_separator() {
        let asm = Assembler::new();
        let sl: Vec<&str> = asm.op_list_separator.split("20 30 40").collect();
        assert_eq!(sl.as_slice(), &["20", "30", "40"]);
        let sl: Vec<&str> = asm.op_list_separator.split("18").collect();
        assert_eq!(sl.as_slice(), &["18"]);
        let sl: Vec<&str> = asm.op_list_separator.split("120, 0x30 40, 023").collect();
        assert_eq!(sl.as_slice(), &["120", "0x30", "40", "023"]);
    }

    #[test]
    fn empty_line() {
        assert_asm("", &[]);
    }

    #[test]
    fn implied_mode() {
        assert_asm("SEI", &[0x78]);
        assert_asm("ASL", &[0x0a]);
    }

    #[test]
    fn immediate_mode() {
        assert_asm("LDA #%00110101", &[0xa9, 0b00110101]);
        assert_asm("LDX #123", &[0xa2, 123]);
        assert_asm("LDY #255", &[0xa0, 0xff]);
    }

    #[test]
    fn zero_page_mode() {
        assert_asm("LDY $8f", &[0xa4, 0x8f]);
    }

    #[test]
    fn zero_page_x_mode() {
        assert_asm("LDA $a0,X", &[0xb5, 0xa0]);
    }

    #[test]
    fn zero_page_y_mode() {
        assert_asm("STX $7a,Y", &[0x96, 0x7a]);
    }

    #[test]
    fn absolute_mode() {
        let mut asm = assert_asm("ROR $3400", &[0x6e, 0x00, 0x34]);
        assert_next(&mut asm, "jmp $2000", &[0x4c, 0x00, 0x20]);
        assert!(asm.resolver.define_symbol("c", 0xfab0).is_ok());
        assert_next(&mut asm, "jmp c", &[0x4c, 0xb0, 0xfa]);
    }

    #[test]
    fn absolute_mode_adc() {
        assert_asm("ADC $2000", &[0x6d, 0x00, 0x20]);
    }

    #[test]
    fn absolute_mode_x() {
        assert_asm("LSR $35f0,X", &[0x5e, 0xf0, 0x35]);
    }

    #[test]
    fn scanning_phase_addmode_optimization_for_undefined_symbols() {
        let mut asm = Assembler::new();
        assert!(!asm.generate_code);
        assert!(asm.process_line("LDA etykieta,X").is_ok());
        assert_eq!(asm.location_counter, 3);
    }

    #[test]
    fn absolute_mode_y() {
        assert_asm("EOR $f7a0,Y", &[0x59, 0xa0, 0xf7]);
    }

    #[test]
    fn indirect_mode() {
        assert_asm("JMP ($ffa0)", &[0x6c, 0xa0, 0xff]);
    }

    #[test]
    fn indirect_mode_x() {
        assert_asm("LDA ($8c,X)", &[0xa1, 0x8c]);
    }

    #[test]
    fn indirect_indexed_y() {
        assert_asm("ORA ($a7),Y", &[0x11, 0xa7]);
    }

    #[test]
    fn relative_mode() {
        assert_asm("BCC -1", &[0x90, u8::from_ne_bytes((-1 as i8).to_ne_bytes())]);
        assert_asm("BVS +8", &[0x70, 8]);
    }

    #[test]
    fn relative_mode_with_label() {
        let mut asm = assert_asm(".org $0607", &[]);
        assert!(asm.resolver.define_symbol("before", 0x0600).is_ok());
        assert!(asm.resolver.define_symbol("after", 0x0613).is_ok());
        assert_eq!(asm.location_counter, 0x607);
        assert_next(&mut asm, "BEQ after", &[0xF0, 0x0A]);
        assert_eq!(asm.location_counter, 0x0609);
        assert_next(&mut asm, "BCC before", &[0x90, u8::from_ne_bytes((-11 as i8).to_ne_bytes())]);
        assert_eq!(asm.location_counter, 0x060B);
    }

    #[test]
    fn set_location_counter() {
        let mut asm = assert_asm("  .ORG $3000 ;origin", &[]);
        assert_eq!(asm.origin.unwrap(), 0x3000);
        assert_eq!(asm.location_counter, 0x3000);
        assert_next(&mut asm, "  .ORG $4000 ;origin", &[]);
        assert_eq!(asm.location_counter, 0x4000);
        assert_eq!(asm.code.len(), 0x1000);
        assert_next(&mut asm, "  *= $5000 ;origin", &[]);
        assert_eq!(asm.location_counter, 0x5000);
        assert_eq!(asm.code.len(), 0x2000);
    }

    #[test]
    fn comments() {
        assert_asm("lda ($8c,X)  ;komentarz", &[0xa1, 0x8c]);
        assert_asm("  ;  komentarz", &[]);
        assert_asm("label: ;komentarz numer 2", &[]);
        assert_asm("LSR $35f0,X ;comment", &[0x5e, 0xf0, 0x35]);
    }

    #[test]
    fn label() {
        let mut asm = assert_asm("Label_001:", &[]);
        assert_next(&mut asm, "LDA ($8c,X)", &[0xa1, 0x8c]);
        assert_next(&mut asm, "Label_002:", &[]);
        assert_eq!(asm.resolver.symbols().get("Label_001").unwrap(), &0);
        assert_eq!(asm.resolver.symbols().get("Label_002").unwrap(), &2);
    }

    #[test]
    fn symbols() {
        let mut asm = Assembler::new();
        assert!(asm.resolver.define_symbol("dziabaDucha", 0xaf02).is_ok());
        asm.init_pass(true);
        assert!(asm.set_location_counter(1000).is_ok());
        assert_next(&mut asm, "TestLabel_01:  SEI   ; disable interrupts ", &[0x78]);
        assert_next(&mut asm, "c:lda dziabaDucha", &[0xad, 0x02, 0xaf]);
        assert_eq!(asm.resolver.symbols().get("TestLabel_01").unwrap(), &1000);
        assert_eq!(asm.resolver.symbols().get("TestLabel_02"), None);
        assert_eq!(asm.code.len(), 4);
        assert_eq!(asm.location_counter, 1004);
    }

    #[test]
    fn emit_bytes() {
        assert_asm(".BYTE 20", &[20]);
        assert_asm(".BYTE $20 45 $4a", &[0x20, 45, 0x4a]);
        assert_asm(".BYTE $20, $3f,$4a ,$23 , 123", &[0x20, 0x3f, 0x4a, 0x23, 123]);
        assert_asm(
            "dcb 0,0,0,0,0,0,0,0,0,$b,$b,$c,$f,$f,$f,$f",
            &[0, 0, 0, 0, 0, 0, 0, 0, 0, 0xb, 0xb, 0xc, 0xf, 0xf, 0xf, 0xf],
        );
    }

    #[test]
    fn emit_words() {
        assert_asm(".word $20ff $23af $fab0 ;komm", &[0xff, 0x20, 0xaf, 0x23, 0xb0, 0xfa]);
        assert_asm(".word $3000 $15ad 1024", &[0x00, 0x30, 0xad, 0x15, 0x00, 0x04]);
    }

    #[test]
    fn lo_byte_modifier() {
        let mut asm = assert_asm("LDA #<$1afc", &[0xa9, 0xfc]);
        assert!(asm.resolver.define_symbol("label", 0x2afe).is_ok());
        assert_next(&mut asm, "LDA #<label", &[0xa9, 0xfe]);
        assert_next(&mut asm, "dcb <label, 2", &[0xfe, 2]);
    }

    #[test]
    fn hi_byte_modifier() {
        let mut asm = assert_asm("LDA #>$1afc", &[0xa9, 0x1a]);
        assert!(asm.resolver.define_symbol("label", 0x3afe).is_ok());
        assert_next(&mut asm, "LDA #>label", &[0xa9, 0x3a]);
        assert_next(&mut asm, "dcb >label, 2", &[0x3a, 2]);
        assert!(asm.resolver.define_symbol("a", 0xfa20).is_ok());
        assert!(asm.resolver.define_symbol("b", 0x10a0).is_ok());
        assert_next(&mut asm, "dcb >a, <b", &[0xfa, 0xa0]);
        assert_next(&mut asm, "dcb <a, >b", &[0x20, 0x10]);
    }

    #[test]
    fn define_symbol() {
        let mut asm = assert_asm(".org $1000", &[]);
        assert!(asm.resolver.define_symbol("init", 0x1234).is_ok());
        assert_next(&mut asm, "lda init", &[0xad, 0x34, 0x12]);
        assert_eq!(asm.location_counter, 0x1003);
    }
}
