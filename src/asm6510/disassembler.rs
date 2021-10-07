use crate::emu6510::{addrmode::AddrMode, mem64k::*, operation::Operation};

pub type Columns = (String, String, String);

pub fn disassemble(memory: &impl Mem64K, pc: &mut u16) -> Columns {
    let mut buf = (format!("{:04X} ", pc), String::new(), String::new());
    let opcode = memory.byte(*pc);
    let operation = Operation::from_opcode(opcode);
    let opsize = operation.len() as u16;
    for i in 0..3 {
        if i < opsize {
            buf.1.push_str(&format!("{:02X} ", memory.byte(*pc + i)));
        } else {
            buf.1.push_str("   ");
        }
    }
    buf.2.push_str(&format!(" {} ", operation.instruction.to_string()));
    let opaddr = *pc + 1;
    buf.2.push_str(&match operation.addrmode {
        AddrMode::Implied => String::from(""),
        AddrMode::Relative => format!("${:04X}", *pc as i32 + (memory.byte(opaddr) as i8) as i32 + 2),
        AddrMode::Immediate => format!("#${:02X}", memory.byte(opaddr)),
        AddrMode::ZeroPage => format!("${:02X}", memory.byte(opaddr)),
        AddrMode::ZeroPageX => format!("${:02X},X", memory.byte(opaddr)),
        AddrMode::ZeroPageY => format!("${:02X},Y", memory.byte(opaddr)),
        AddrMode::IndexedIndirectX => format!("(${:02X},X)", memory.byte(opaddr)),
        AddrMode::IndirectIndexedY => format!("(${:02X}),Y", memory.byte(opaddr)),
        AddrMode::Indirect => format!("(${:04X})", memory.word(opaddr)),
        AddrMode::Absolute => format!("${:04X}", memory.word(opaddr)),
        AddrMode::IndexedX => format!("${:04X},X", memory.word(opaddr)),
        AddrMode::IndexedY => format!("${:04X},Y", memory.word(opaddr)),
    });
    *pc += opsize;
    buf
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mode_absolute() {
        let mut memory = Ram64K::new();
        let mut pc: u16 = 0x1000;
        memory.set_byte(pc, 0xad);
        memory.set_word(pc + 1, 0x1234);
        assert_eq!(
            disassemble(&memory, &mut pc),
            ("1000 ".to_string(), "AD 34 12 ".to_string(), " LDA $1234".to_string())
        );
    }
}
