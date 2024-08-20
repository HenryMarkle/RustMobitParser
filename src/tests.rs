use anyhow::Result;
use log::info;
use simple_logger::SimpleLogger;

use crate::{ast::{self, Expression, PostOperator}, tokens};

#[test]
pub fn scripts() -> Result<()> {
    use std::fs;
    
    SimpleLogger::new().init()?;

    let dirs = fs::read_dir(r#"C:\Users\Henry Markle\Projects\RustMobitParser\test"#)?;

    let scripts: Vec<_> = dirs
        .flatten()
        .filter(|e| e.file_type().unwrap().is_file())
        .map(|e| (e.file_name().to_string_lossy().into_owned(), fs::read_to_string(e.path())))
        .filter(|(_, script)| script.is_ok())
        .collect();

    for (name, script) in scripts {
        info!("parsing script \"{:?}\"", name);

        let text = script.unwrap();

        let t = tokens::tokenize(&text)?;
    
        let _ = ast::parse_script(t)?;
    }

    Ok(())
}

#[test]
pub fn function() -> Result<()> {    
    let t1 = tokens::tokenize(
        "on function
        end"
    )?;

    let t2 = tokens::tokenize(
        "on function me
        end function"
    )?;
    
    let t3 = tokens::tokenize(
        "on function me
            write()
            1 + 1
        end function"
    )?;

    let t4 = tokens::tokenize(
        "on function me, ln, depth
            write()
            1 + 1
        end"
    )?;
    
    let t5 = tokens::tokenize(
        "on function me, ln: number, depth
            write()
            1 + 1
        end"
    )?;
    
    let t6 = tokens::tokenize(
        "on function(me, ln: number, depth)
            write()
            1 + 1
        end"
    )?;

    let _ = ast::parse_function(&t1, 0)?;
    let _ = ast::parse_function(&t2, 0)?;
    let _ = ast::parse_function(&t3, 0)?;
    let _ = ast::parse_function(&t4, 0)?;
    let _ = ast::parse_function(&t5, 0)?;
    let _ = ast::parse_function(&t6, 0)?;

    Ok(())
}

#[test]
pub fn repeat_statement() -> Result<()> {    
    let t1 = tokens::tokenize(
        "repeat with i = 1 to 11 then
        lol()
        end repeat"
    )?;

    let t2 = tokens::tokenize(
        "repeat with i = 10 down to 1 then
          lol()
        end repeat"
    )?;

    let t3 = tokens::tokenize(
        "repeat with i in list then
          lol()
        end repeat"
    )?;

    let t4 = tokens::tokenize(
        "repeat while depth < 3 then
         digDeeper()
        end repeat"
    )?;

    let _ = ast::parse_repeat_statement(&t1, 0)?;
    let _ = ast::parse_repeat_statement(&t2, 0)?;
    let _ = ast::parse_repeat_statement(&t3, 0)?;
    let _ = ast::parse_repeat_statement(&t4, 0)?;
    
    Ok(())
}

#[test]
pub fn case_statement() -> Result<()> {
    let t1 = tokens::tokenize(
        "case var of
        \"standard\":
          1 + 1
        \"varied\", \"soft\":
          2 + 2

        otherwise:

          nah()
        end case"
    )?;

    let _ = ast::parse_switch_statement(&t1, 0)?;
    
    Ok(())
}

#[test]
pub fn if_single_line_statement() -> Result<()> {    
    let t1 = tokens::tokenize(
        "if var = 1 then callFunc() else var = 2 + 2\n"
    )?;

    let _ = ast::parse_condition(&t1, 0)?;
    
    Ok(())
}

#[test]
pub fn if_statement() -> Result<()> {
    let t1 = tokens::tokenize(
        "if var = 1 then 
          var = 1 + 1
        else 
          var = 2 + 2
        end if"
    )?;

    let _ = ast::parse_condition(&t1, 0)?;
    
    Ok(())
}

#[test]
pub fn property_variables() -> Result<()> {
    
    let t1 = tokens::tokenize("property gProps, gVar1")?;
    
    let _ = ast::parse_statement(&t1, 0)?;

    Ok(())
}

#[test]
pub fn global_variables() -> Result<()> {
    let t1 = tokens::tokenize("global gProps, gVar1")?;
    
    let _ = ast::parse_statement(&t1, 0)?;

    Ok(())
}

#[test]
pub fn expression() -> Result<()> {
    let t1 = tokens::tokenize("[ #name: \"Henry\" & \"Markle\", #repeat: [1, 2, 3, 4, TRUE or FALSE], #sym: point(0, 1) ]")?;
    let t2 = tokens::tokenize("[ #symb, \"STR\", 0, 1.2, rect(0,0,1,1), [] ]")?;
    let t3 = tokens::tokenize("var.member(1 + num)[2][#name]")?;

    let _ = ast::parse_expression(&t1, 0, 0, true)?;
    let _ = ast::parse_expression(&t2, 0, 0, true)?;
    let _ = ast::parse_expression(&t3, 0, 0, true)?;
    
    Ok(())
}

#[test]
pub fn word_range_indexing() -> Result<()> {
    let tokens1 = tokens::tokenize("char 1 to 3 of var")?;
    let tokens2 = tokens::tokenize("word 1 to 3 of var")?;
    let tokens3 = tokens::tokenize("line 1 to 3 of var")?;
    let tokens4 = tokens::tokenize("item 1 to 3 of var")?;
    
    let ast1 = ast::parse_expression(&tokens1, 0, 0, true)?;
    let _ = ast::parse_expression(&tokens2, 0, 0, true)?;
    let _ = ast::parse_expression(&tokens3, 0, 0, true)?;
    let _ = ast::parse_expression(&tokens4, 0, 0, true)?;

    assert_ne!(ast1.1, 0);

    Ok(())
}

#[test]
pub fn word_indexing() -> Result<()> {
    let tokens1 = tokens::tokenize("char 1 of var")?;
    let tokens2 = tokens::tokenize("word 1 of var")?;
    let tokens3 = tokens::tokenize("line 1 of var")?;
    let tokens4 = tokens::tokenize("item 1 of var")?;
    
    let ast1 = ast::parse_expression(&tokens1, 0, 0, true)?;
    let _ = ast::parse_expression(&tokens2, 0, 0, true)?;
    let _ = ast::parse_expression(&tokens3, 0, 0, true)?;
    let _ = ast::parse_expression(&tokens4, 0, 0, true)?;

    assert_ne!(ast1.1, 0);

    match ast1.0 {
        Expression::PostOperation { left, operator } => {
            if let PostOperator::Index(i) = operator {
                if let Expression::Integer(int) = *i {
                    assert_eq!(int, 1);
                } else {
                    panic!("index was not an integer");
                }
            } else {
                panic!("operator was not an indexer");
            }

            if let Expression::PostOperation { left, operator } = *left {
                if let Expression::Identifier(iden) = *left {
                    assert!(iden.eq_ignore_ascii_case("var"));
                } else {
                    panic!("was not an identifer");
                }

                if let PostOperator::MemberAccess(member) = operator {
                    assert!(member.eq_ignore_ascii_case("char"));
                } else {
                    panic!("was not a member access operator");
                }
            } else {
                panic!("invalid member access");
            }
        },

        _ => {
            panic!("invalid operator")
        }
    }

    Ok(())
}

#[test]
pub fn typed_assignment() -> Result<()> {
    let t = tokens::tokenize("var: number = 1")?;
    
    let s = ast::parse_assignment(&t, 0)?;

    assert_ne!(s.1, 0);

    Ok(())
}

#[test]
pub fn simple_assignment() -> Result<()> {
    let t = tokens::tokenize("var = 1")?;
    
    let s = ast::parse_assignment(&t, 0)?;

    assert_ne!(s.1, 0);

    Ok(())
}

#[test]
pub fn type_casting() -> Result<()> {
    let t = tokens::tokenize("type return: number")?;
    
    let s = ast::parse_statement(&t, 0)?;

    assert_ne!(s.1, 0);

    Ok(())
}