use super::operand::{HI_BYTE_MODIFIER, LO_BYTE_MODIFIER};
use regex::Regex;

pub const SYMBOL: &str = "[a-z]\\w*";
pub const LABEL: &str = "^(?:([a-z]\\w*):)?\\s*";
pub const COMMENT: &str = "(?:;.*)?$";
pub const SEPARATOR: &str = "\\s*,?\\s*";

pub struct AsmPatterns {
    pub empty_line: Regex,
    pub cmd_set_location_counter: Regex,
    pub cmd_emit_bytes: Regex,
    pub cmd_emit_words: Regex,
    pub ins_implied: Regex,
    pub ins_immediate: Regex,
    pub ins_branch: Regex,
    pub ins_absolute: Regex,
    pub ins_absolute_indexed_x: Regex,
    pub ins_absolute_indexed_y: Regex,
    pub ins_indirect: Regex,
    pub ins_indexed_indirect_x: Regex,
    pub ins_indirect_indexed_y: Regex,
}

fn rx(pattern: &str) -> Regex {
    Regex::new(&format!("(?i){}{}\\s*{}", LABEL, pattern, COMMENT)).unwrap()
}

impl AsmPatterns {
    pub fn new() -> AsmPatterns {
        let org_cmd = String::from("((?:\\.ORG\\s+)|(?:\\*\\s*=\\s*))");
        let byte_cmd = String::from("(\\.BYTE|DCB)\\s+");
        let word_cmd = String::from("(\\.WORD)\\s+");
        let hex_num = String::from("\\$[\\d|a-f]{1,4}");
        let dec_num = String::from("\\d{1,5}");
        let bin_num = String::from("%[01]{1,16}");
        let mnemonic = String::from("([a-z]{3})\\s*");
        let num_or_symbol = format!("(?:{})|(?:{})|(?:{})|(?:{})", hex_num, dec_num, bin_num, SYMBOL);
        let lo_hi_prefix = format!("[{}|{}]?", LO_BYTE_MODIFIER, HI_BYTE_MODIFIER);
        let operand = format!("({}(?:{}))\\s*", lo_hi_prefix, num_or_symbol);
        let operand_list = format!("((?:(?:{}(?:{})){})+)\\s*", lo_hi_prefix, num_or_symbol, SEPARATOR);
        let branch_mnemonic = String::from("(BCC|BCS|BNE|BEQ|BMI|BPL|BVC|BVS)\\s*");
        let branch_target = format!("((?:[+|-]?\\d{{1,3}})|(?:{}))\\s*", SYMBOL);
        AsmPatterns {
            empty_line: rx(""),
            cmd_set_location_counter: rx(&format!("{}{}", org_cmd, operand)),
            cmd_emit_bytes: rx(&format!("{}{}", byte_cmd, operand_list)),
            cmd_emit_words: rx(&format!("{}{}", word_cmd, operand_list)),
            ins_implied: rx(&format!("{}", mnemonic)),
            ins_immediate: rx(&format!("{}#{}", mnemonic, operand)),
            ins_branch: rx(&format!("{}{}", branch_mnemonic, branch_target)),
            ins_absolute: rx(&format!("{}{}", mnemonic, operand)),
            ins_absolute_indexed_x: rx(&format!("{}{},x", mnemonic, operand)),
            ins_absolute_indexed_y: rx(&format!("{}{},y", mnemonic, operand)),
            ins_indirect: rx(&format!("{}\\({}\\)", mnemonic, operand)),
            ins_indexed_indirect_x: rx(&format!("{}\\({},x\\)", mnemonic, operand)),
            ins_indirect_indexed_y: rx(&format!("{}\\({}\\),y", mnemonic, operand)),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::asm6510::tokens::Tokens;

    use super::*;

    fn assert_line(regex: &Regex, line: &str, label: Option<&str>, operation: Option<&str>, operand: Option<&str>) {
        match regex.captures(line) {
            Some(caps) => {
                let t = Tokens::new(caps);
                assert_eq!(t.label(), label.as_deref());
                assert_eq!(t.operation(), operation.as_deref());
                assert_eq!(t.operand(), operand.as_deref());
                // assert_eq!(caps.get(1).map(|m| m.as_str()).as_deref(), label.as_deref());
                // assert_eq!(caps.get(2).map(|m| m.as_str()).as_deref(), operation.as_deref());
                // assert_eq!(caps.get(3).map(|m| m.as_str()).as_deref(), operand.as_deref());
            }
            None => assert!(false, "line: \"{}\" matching failed", line),
        }
    }

    #[test]
    fn match_label() {
        assert_line(&AsmPatterns::new().empty_line, "label:", Some("label"), None, None);
    }

    #[test]
    fn match_emit_bytes() {
        assert_line(
            &AsmPatterns::new().cmd_emit_bytes,
            ".BYTE 20 30",
            None,
            Some(".BYTE"),
            Some("20 30"),
        );
    }

    #[test]
    fn match_emit_words() {
        assert_line(
            &AsmPatterns::new().cmd_emit_words,
            ".word $20ff $23af $fab0 ;ddd",
            None,
            Some(".word"),
            Some("$20ff $23af $fab0"),
        );
    }

    #[test]
    fn match_implied() {
        let p = AsmPatterns::new().ins_implied;
        assert_line(&p, "    inc", None, Some("inc"), None);
        assert_line(&p, "SEI", None, Some("SEI"), None);
        assert_line(&p, "label1: SEI", Some("label1"), Some("SEI"), None);
    }

    #[test]
    fn match_immediate() {
        let p = AsmPatterns::new().ins_immediate;
        assert_line(&p, "lda #$AF", None, Some("lda"), Some("$AF"));
        assert_line(&p, "ldx #128", None, Some("ldx"), Some("128"));
    }

    #[test]
    fn match_absolute() {
        let p = AsmPatterns::new().ins_absolute;
        assert_line(&p, "LDY $8f", None, Some("LDY"), Some("$8f"));
        assert_line(&p, "jmp $2000", None, Some("jmp"), Some("$2000"));
    }

    #[test]
    fn match_absolute_x() {
        let p = AsmPatterns::new().ins_absolute_indexed_x;
        assert_line(&p, "LDA $a0,X", None, Some("LDA"), Some("$a0"));
    }

    #[test]
    fn match_comment() {
        let ap = AsmPatterns::new();
        assert_line(&ap.empty_line, " ", None, None, None);
        assert_line(&ap.empty_line, " ;komentarz", None, None, None);
        assert_line(&ap.ins_implied, "  CLI ;komentarz", None, Some("CLI"), None);
        assert_line(&ap.ins_indexed_indirect_x, "  LDA ($8c,X) ;asd", None, Some("LDA"), Some("$8c"));
    }
}
