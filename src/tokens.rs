use std::{
    num::{ParseFloatError, ParseIntError},
    rc::Rc
};
use thiserror;
use log::error;

#[derive(Debug, Clone)]
pub enum LogicalOperator {
    Or, And
}

#[derive(Debug, Clone)]
pub enum ArithmeticalOperator {
    Add, Subtract, Multiply, Divide
}

impl LogicalOperator {
    pub fn to_string(&self) -> String {
        match self {
            LogicalOperator::Or => "or".into(),
            LogicalOperator::And => "and".into()
        }
    }
}

impl ArithmeticalOperator {
    pub fn to_string(&self) -> String {
        match self {
            ArithmeticalOperator::Add => "add".into(),
            ArithmeticalOperator::Subtract => "subtract".into(),
            ArithmeticalOperator::Multiply => "multiply".into(),
            ArithmeticalOperator::Divide => "divide".into()
        }
    }
}

#[derive(Debug)]
pub enum Token {
    OpenBracket,
    CloseBracket,

    OpenParenthesis,
    CloseParenthesis,

    Comma,
    Colon,
    Concatenation,
    LogicalOperator(LogicalOperator),
    ArithmeticalOperator(ArithmeticalOperator),

    Void,

    String(Rc<str>),
    Integer(i32),
    Float(f32),
    Identifier(Rc<str>),
    GlobalCall(Rc<str>),
    Constant(Rc<str>)
}

#[derive(Debug, thiserror::Error)]
pub enum TokenizeError {

    #[error("empty expression")]
    EmptyExpression,

    #[error("empty identifier")]
    EmptyIdentifier,

    #[error("double decimal point")]
    DoubleDecimalPoint,

    #[error("failed to parse integer")]
    IntParse {
        #[from] err: ParseIntError,
    },

    #[error("failed to parse float")]
    FloatParse {
        #[from] err: ParseFloatError,
    },

    #[error("unexpected token \"{character}\"")]
    UnexpectedToken { character: char }
}

pub fn tokenize<T : AsRef<str>>(string: T) -> Result<Vec<Token>, TokenizeError> {
    let str_ref = string.as_ref();

    if str_ref.is_empty() { return Err(TokenizeError::EmptyExpression); }

    let mut chars = str_ref.chars().peekable();

    let mut tokens = vec![];

    while let Some(current) = chars.next() {
        match current {
            '[' => { tokens.push(Token::OpenBracket); },
            ']' => { tokens.push(Token::CloseBracket); },

            '(' => { tokens.push(Token::OpenParenthesis); },
            ')' => { tokens.push(Token::CloseParenthesis); },

            ',' => { tokens.push(Token::Comma); },
            ':' => { tokens.push(Token::Colon); },

            '&' => {
                if let Some(next) = chars.peek() {
                    if *next == '&' {
                        tokens.push(Token::LogicalOperator(LogicalOperator::And));

                        chars.next();
                        continue;
                    }
                }

                tokens.push(Token::Concatenation);
            },

            '|' => {
                if let Some(next) = chars.peek() {
                    if *next == '|' {
                        tokens.push(Token::LogicalOperator(LogicalOperator::Or));

                        chars.next();
                        continue;
                    }
                }

                return Err(TokenizeError::UnexpectedToken { character: '|' });
            },

            '+' => { tokens.push(Token::ArithmeticalOperator(ArithmeticalOperator::Add)); },
            '-' => { tokens.push(Token::ArithmeticalOperator(ArithmeticalOperator::Subtract)); },
            '*' => { tokens.push(Token::ArithmeticalOperator(ArithmeticalOperator::Multiply)); },
            '/' => { tokens.push(Token::ArithmeticalOperator(ArithmeticalOperator::Divide)); },

            '0' | '1' | '2' | '3' |
            '4' | '5' | '6' | '7' |
            '8' | '9' | '.' => {
                let mut buffer = String::with_capacity(1);
                buffer.push(current);
                let mut is_float = false;

                while let Some(next) = chars.peek() {
                    if next.is_digit(10) { buffer.push(*next); chars.next(); }
                    else if *next == '.' {
                        if is_float {
                            return Err(TokenizeError::DoubleDecimalPoint);
                        } else {
                            buffer.push(*next);
                            chars.next();
                            is_float = true;
                        }
                    } else { break; }
                }

                if is_float {
                    match buffer.parse::<f32>() {
                        Ok(number) => { tokens.push(Token::Float(number)); },
                        Err(e) => { return Err(TokenizeError::FloatParse { err: e }); }
                    }
                } else {
                    match buffer.parse::<i32>() {
                        Ok(number) => { tokens.push(Token::Integer(number)); },
                        Err(e) => { return Err(TokenizeError::IntParse { err: e }); }
                    }
                }
            },

            '#' => {
                let mut buffer = String::with_capacity(1);

                while let Some(next) = chars.peek() {
                    if next.is_alphanumeric() || *next == '_' {
                        buffer.push(*next);
                        chars.next();
                    } else { break; }
                }

                if buffer.is_empty() {
                    return Err(TokenizeError::EmptyIdentifier);
                }

                tokens.push(Token::Identifier(buffer.into()));
            },

            '"' => {
                let mut buffer = String::with_capacity(1);

                while let Some(next) = chars.next() {
                    if next == '"' {
                        break;
                    } else {
                        buffer.push(next);
                    }
                }

                tokens.push(Token::String(buffer.into()));
            },

            _ => {
                let mut buffer = String::with_capacity(1);

                if !current.is_alphanumeric() && current != '_' {
                    return Err(TokenizeError::UnexpectedToken { character: current });
                }

                while let Some(next) = chars.next() {
                    if next.is_alphanumeric() || next == '_' {
                         buffer.push(next);
                    } else { break; }
                }

                if buffer == "void" {
                    tokens.push(Token::Void);
                } else if current == '(' {
                    tokens.push(Token::GlobalCall(buffer.into()));
                } else {
                    tokens.push(Token::Constant(buffer.into()));
                }
            }
        }
    }

    Ok(tokens)
}
