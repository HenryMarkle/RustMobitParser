use std::{
    collections::HashMap,
    rc::Rc
};
use std::f32::consts::PI;
use std::ops::Deref;
use crate::tokens::{ArithmeticalOperator, LogicalOperator, Token};
use thiserror;
use log::{debug, error};

#[derive(Debug)]
pub enum LogicalOperation {
    And, Or
}

#[derive(Debug)]
pub enum ArithmeticalOperation {
    Addition,
    Subtraction,
    Multiplication,
    Division
}

#[derive(Debug)]
pub enum Expression {
    String(Rc<str>),
    Integer(i32),
    Float(f32),
    GlobalCall {
        name: Rc<str>,
        args: Box<[Expression]>
    },
    LinearList(Box<[Expression]>),
    PropertyList(HashMap<Rc<str>, Expression>),

    LogicalOperation {
        operation: LogicalOperator,
        left: Box<Expression>,
        right: Box<Expression>
    },

    ArithmeticalOperation {
        operation: ArithmeticalOperation,
        left: Box<Expression>,
        right: Box<Expression>
    },

    Void
}

impl LogicalOperation {
    pub fn to_string(&self) -> String {
        match self {
            LogicalOperation::And => "and".into(),
            LogicalOperation::Or => "or".into()
        }
    }
}

impl ArithmeticalOperation {
    pub fn to_string(&self) -> String {
        match self {
            ArithmeticalOperation::Addition => "addition".into(),
            ArithmeticalOperation::Subtraction => "subtraction".into(),
            ArithmeticalOperation::Multiplication => "multiplication".into(),
            ArithmeticalOperation::Division => "division".into()
        }
    }
}

impl Expression {
    pub fn to_json_string(&self) -> String {
        match self {
            Expression::String(string) => format!("\"{}\"", string),
            Expression::Integer(int) => format!("{}", int),
            Expression::Float(float) => format!("{}", float),
            Expression::Void => "void".into(),
            Expression::GlobalCall { name, args } => {
                let args_str: Vec<String> = args
                    .iter()
                    .map(|n| n.to_json_string())
                    .collect();

                format!("{}({})", &name, args_str.join(","))
            },
            Expression::LinearList(list) => {
                let list_str: Vec<String> = list
                    .iter()
                    .map(|n| n.to_json_string())
                    .collect();

                format!("[{}]", list_str.join(","))
            },
            Expression::PropertyList(props) => {
                let props_list: Vec<String> = props
                    .iter()
                    .map(|(key, value)| format!("\"{}\":{}", &key, value.to_json_string()))
                    .collect();

                String::from("{")
                    + &format!("{}", props_list.join(","))
                    + "}"
            },
            Expression::LogicalOperation {
                operation,
                left,
                right
            } => {
                String::from("{")
                    + &format!("\"logical_operation\":{},\"left\":{},\"right\":{}",
                               operation.to_string(),
                               left.to_json_string(),
                               right.to_json_string()
                    )
                    + "}"
            },
            Expression::ArithmeticalOperation {
                operation,
                left,
                right
            } => {
                String::from("{")
                    + &format!("\"arithmetical_operation\":{},\"left\":{},\"right\":{}",
                               operation.to_string(),
                               left.to_json_string(),
                               right.to_json_string()
                    )
                    + "}"
            }
        }
    }

    pub fn to_json_string_pretty(&self) -> String {
        match self {
            Expression::String(string) => format!("\"{}\"", string),
            Expression::Integer(int) => format!("{}", int),
            Expression::Float(float) => format!("{}", float),
            Expression::Void => "void".into(),
            Expression::GlobalCall { name, args } => {
                let args_str: Vec<String> = args
                    .iter()
                    .map(|n| n.to_json_string())
                    .collect();

                format!("{}({})", &name, args_str.join(", "))
            },
            Expression::LinearList(list) => {
                let list_str: Vec<String> = list
                    .iter()
                    .map(|n| n.to_json_string())
                    .collect();

                format!("[\n\t{}\n]", list_str.join(",\n\t"))
            },
            Expression::PropertyList(props) => {
                let props_list: Vec<String> = props
                    .iter()
                    .map(|(key, value)| format!("\"{}\": {}", &key, value.to_json_string()))
                    .collect();

                String::from("{\n\t")
                    + &format!("{}", props_list.join(",\n\t"))
                    + "}"
            },
            Expression::LogicalOperation {
                operation,
                left,
                right
            } => {
                String::from("{")
                    + &format!("\n\t\"logical_operation\":{},\n\t\"left\":{},\n\t\"right\":{}",
                               operation.to_string(),
                               left.to_json_string_pretty(),
                               right.to_json_string_pretty()
                )
                    + "}"
            },
            Expression::ArithmeticalOperation {
                operation,
                left,
                right
            } => {
                String::from("{")
                    + &format!("\n\t\"arithmetical_operation\":{},\n\t\"left\":{},\n\t\"right\":{}",
                               operation.to_string(),
                               left.to_json_string_pretty(),
                               right.to_json_string_pretty()
                )
                    + "}"
            }
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum TokensParseError {
    #[error("unexpected token: {:?}", character)]
    UnexpectedToken { character: Option<char> },

    #[error("expected token: {}", character)]
    ExpectedToken { character: char },

    #[error("unexpected end of tokens")]
    UnexpectedEnd,

    #[error("imbalanced collection")]
    ImbalancedCollection,

    #[error("collection must be either a linear list or a property list, not both.")]
    ObscureCollectionType,

    #[error("no tokens")]
    EmptyTokens,

    #[error("out of range")]
    OutOfRange,

    #[error("unsatisfied logical operator")]
    UnsatisfiedLogicalOperator(LogicalOperator),

    #[error("unsatisfied arithmetical operator")]
    UnsatisfiedArithmeticalOperator(ArithmeticalOperator),

    #[error("undefined constant \"{}\"", constant)]
    UndefinedConstant { constant: Rc<str> }
}

fn parse_tokens_helper(tokens: &[Token], cursor: usize) -> Result<(Expression, usize), TokensParseError> {
    if tokens.is_empty() { return Err(TokensParseError::EmptyTokens); }

    let length = tokens.len();

    let mut begin = cursor;

    if begin >= length { return Err(TokensParseError::OutOfRange); }

    debug!("parsing at ({})", begin);

    let current = &tokens[begin];

    match current {
        Token::OpenBracket => {
            debug!("parsing a collection at ({})", begin);

            let mut sub_nodes = vec![];
            let mut map = HashMap::new();
            let mut commad = true;
            let mut is_prop = false;
            begin += 1;

            while begin < length {
                match &tokens[begin] {

                    Token::CloseBracket => {
                        // are trailing commas allowed?
                        if commad {
                            error!("unexpected trailing comma at ({})", begin);
                            return Err(TokensParseError::UnexpectedToken { character: Some(',') });
                        }

                        if is_prop {
                            debug!("done parsing property list at ({})", begin);
                            return Ok((Expression::PropertyList(map), begin));
                        }

                        debug!("done parsing linear list at ({})", begin);
                        return Ok((Expression::LinearList(sub_nodes.into()), begin));
                    },

                    Token::Colon => {
                        if begin == cursor + 1 {
                            is_prop = true;
                        } else if !is_prop {
                            error!("found an illegal colon at ({})", begin);
                            return Err(TokensParseError::UnexpectedToken { character: Some(',') });
                        }
                    },

                    Token::Identifier(key) => {
                        debug!("parsing an identifier at ({})", begin);

                        if !commad {
                            error!("expected a comma at ({})", begin);
                            return Err(TokensParseError::ExpectedToken { character: ',' });
                        }
                        commad = false;

                        if !is_prop {
                            if !sub_nodes.is_empty() {
                                error!("found a property key while parsing a linear list at ({})", begin);
                                return Err(TokensParseError::ObscureCollectionType);
                            }

                            debug!("collection is a property list at ({})", begin);
                            is_prop = true;
                        }

                        let colon_pos = begin + 1;
                        let value_pos = colon_pos + 1;

                        if value_pos >= length { return Err(TokensParseError::UnexpectedEnd); }

                        match &tokens[colon_pos] {
                            Token::Colon => (),
                            _ => {
                                error!("property key wasn't followed by a colon at ({})", begin);
                                return Err(TokensParseError::ExpectedToken { character: ':' });
                            }
                        }

                        debug!("checking property value at ({})", begin);

                        match &tokens[value_pos] {
                            Token::CloseBracket | Token::CloseParenthesis | Token::Colon |
                            Token::Comma | Token::Identifier(_) => {
                                error!("illegal token for a property value at ({})", begin);
                                return Err(TokensParseError::UnexpectedToken { character: None });
                            },

                            _ => {
                                debug!("parsing a property value sub-expression at ({})", value_pos);
                                let (node, reached) = parse_tokens_helper(&tokens, value_pos)?;

                                map.insert(Rc::clone(key), node);
                                begin = reached;
                                debug!("parsing property value sub-expression done at ({})", begin);

                            }
                        }
                    },

                    Token::Comma => {
                        if commad {
                            error!("double comma at ({})", begin);
                            return Err(TokensParseError::UnexpectedToken { character: Some(',') });
                        }
                        commad = true;
                    },

                    _ => {
                        if !commad {
                            error!("expected a comma at ({})", begin);
                            return Err(TokensParseError::ExpectedToken { character: ',' });
                        }

                        commad = false;

                        if is_prop {
                            error!("found a linear list item while parsing a property list at ({})", begin);
                            return Err(TokensParseError::ObscureCollectionType);
                        }

                        debug!("parsing a linear list sub-expression at ({})", begin);
                        let (node, reached) = parse_tokens_helper(&tokens, begin)?;

                        sub_nodes.push(node);
                        begin = reached;
                        debug!("parsing linear list sub-expression done at ({})", begin);
                    }
                };

                begin += 1;
            };

            error!("expected the collection to end but it didn't");
            return Err(TokensParseError::ImbalancedCollection);
        },
        Token::CloseBracket => {
            error!("unexpected token at ({})", begin);
            return Err(TokensParseError::UnexpectedToken { character: Some(']') });
        },
        Token::CloseParenthesis => {
            error!("unexpected token at ({})", begin);
            return Err(TokensParseError::UnexpectedToken { character: Some(')') });
        },
        Token::OpenParenthesis => {
            error!("unexpected token at ({})", begin);
            return Err(TokensParseError::UnexpectedToken { character: Some('(') });
        },
        Token::Comma => {
            error!("unexpected token at ({})", begin);
            return Err(TokensParseError::UnexpectedToken { character: Some(',') });
        },
        Token::Colon => {
            error!("unexpected token at ({})", begin);
            return Err(TokensParseError::UnexpectedToken { character: Some(':') });
        },
        Token::Concatenation => {
            error!("unexpected token at ({})", begin);
            return Err(TokensParseError::UnexpectedToken { character: Some('&') });
        },
        Token::Identifier(_) => {
            error!("unexpected token at ({})", begin);
            return Err(TokensParseError::UnexpectedToken { character: Some('#') });
        },
        Token::Void => {
            debug!("parsing void at ({})", begin);
            return Ok((Expression::Void, begin));
        },
        Token::String(string) => {
            debug!("parsing a string at ({})", begin);

            let mut buffer = String::from(string.as_ref());

            let mut concatinated = false;

            let mut next = begin + 1;

            while next < length {
                match &tokens[next] {
                    Token::Comma |
                    Token::CloseParenthesis |
                    Token::CloseBracket => break,

                    Token::Concatenation => {
                        if concatinated {
                            return Err(TokensParseError::UnexpectedToken { character: Some('&') });
                        }

                        concatinated = true;
                    },

                    Token::String(next_string) => {
                        if !concatinated {
                            return Err(TokensParseError::ExpectedToken { character: '&' });
                        }
                        concatinated = false;

                        buffer.push_str(next_string);
                    },

                    Token::Integer(i) => {
                        if !concatinated {
                            return Err(TokensParseError::ExpectedToken { character: '&' });
                        }
                        concatinated = false;

                        let formatted = format!("{}", i);
                        buffer.push_str(&formatted);
                    },

                    Token::Float(f) => {
                        if !concatinated {
                            return Err(TokensParseError::ExpectedToken { character: '&' });
                        }
                        concatinated = false;

                        let formatted = format!("{}", f);
                        buffer.push_str(&formatted);
                    },

                    _ => {
                        return Err(TokensParseError::UnexpectedToken { character: None });
                    }
                }

                next += 1;
            }

            if concatinated {
                error!("invalid string concatenation (trailing &) at ({})", next);
                return Err(TokensParseError::UnexpectedEnd);
            }

            return Ok((Expression::String(buffer.into()), next - 1));
        },
        Token::Integer(int) => {
            debug!("parsing an integer at ({})", begin);
            return Ok((Expression::Integer(*int), begin));
        },
        Token::Float(float) => {
            debug!("parsing a float at ({})", begin);
            return Ok((Expression::Float(*float), begin))
        },
        Token::Constant(constant) => {
            debug!("parsing a constant at ({})", begin);

            return match constant.deref() {
                "RETURN" => Ok((Expression::String( "\n".into()), begin)),
                "SPACE"  => Ok((Expression::String(  " ".into()), begin)),
                "PI"     => Ok((Expression::Float(PI), begin)),

                _ => Err(TokensParseError::UndefinedConstant { constant: Rc::clone(constant) })
            }
        },

        Token::GlobalCall(name) => {
            debug!("parsing a global call at ({})", begin);

            let open_pos = begin + 1;

            if open_pos >= length {
                error!("expected an opening parenthesis at ({})", open_pos);
                return Err(TokensParseError::UnexpectedEnd);
            }

            match &tokens[open_pos] {
                Token::OpenParenthesis => (),
                _ => {
                    error!("expected an opening parenthesis at ({})", open_pos);
                    return Err(TokensParseError::ExpectedToken { character: '(' });
                }
            };

            let mut args = vec![];
            let mut commad = true;

            begin += 2;

            while begin < length {

                match &tokens[begin] {
                    Token::CloseParenthesis => {
                        if commad {
                            error!("unexpected trailing comma at ({})", begin);
                            return Err(TokensParseError::UnexpectedToken { character: Some(',') });
                        }

                        debug!("global call arguments parsing done at ({})", begin);
                        return Ok((Expression::GlobalCall { name: Rc::clone(name), args: args.into() }, begin));
                    },

                    Token::Comma => {
                        if commad {
                            error!("unexpected comma at ({})", begin);
                            return Err(TokensParseError::UnexpectedToken { character: Some(',') });
                        }

                        commad = true;
                    },

                    _ => {
                        if !commad {
                            error!("expected a comma at ({})", begin);
                            return Err(TokensParseError::ExpectedToken { character: ',' });
                        }

                        commad = false;

                        debug!("parsing global call argument #{} at ({})", args.len(), begin);
                        let (node, reached) = parse_tokens_helper(&tokens, begin)?;

                        args.push(node);
                        begin = reached;
                        debug!("parsing global call argument #{} done at ({})", args.len(), begin);

                    }
                }

                begin += 1;
            }

            error!("expected the global call arguments to end but they didn't");
            return Err(TokensParseError::ImbalancedCollection);
        },

        Token::LogicalOperator(op) => {
            return Err(TokensParseError::UnsatisfiedLogicalOperator(op.clone()));
        },

        Token::ArithmeticalOperator(op) => {
            return Err(TokensParseError::UnsatisfiedArithmeticalOperator(op.clone()));
        }
    }
}

pub fn parse_tokens<T : AsRef<[Token]>>(tokens: T) -> Result<Expression, TokensParseError> {
    match parse_tokens_helper(tokens.as_ref(), 0) {
        Ok((node, _)) => Ok(node),
        Err(e) => Err(e)
    }
}
