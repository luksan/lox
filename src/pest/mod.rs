#[derive(pest_derive::Parser, Debug)]
#[grammar = "pest/lox.pest"]
struct LoxGrammar;


#[cfg(test)]
mod test_pest {
    use pest::Parser;
    use crate::pest::{LoxGrammar, Rule};

    #[test]
    fn parse_debug() {
        pest::set_error_detail(true);
        let x = LoxGrammar::parse(Rule::lox, "while (");
        if let Err(e) = &x {
            println!("{e}");
        }
        println!("{x:#?}");
    }
}