use log::error;
use std::{
    num::{ParseFloatError, ParseIntError}, ops::Deref, rc::Rc
};
use thiserror;

#[derive(Debug, Clone)]
pub enum Operator {
    Dot,                    // .
    Concatenation,          // &
    SpaceConcatenation,     // &&
    Not,                    // not
    Or,                     // or
    And,                    // and
    Addition,               // +
    Subtraction,            // -
    Multiplication,         // *
    Division,               // /
    Mod,                    // %
    Inequality,             // <>
    Greater,                // >    
    Smaller,                // <
    GreaterOrEqual,         // >=
    SmallerOrEqual,         // <=
    AssignmentOrEquality,   // =
    Contains,               // contains
    Starts                  // starts
}

#[derive(Debug)]
pub enum Keyword {
    Global,
    Switch,
    Function,
    Void
}

#[derive(Debug)]
pub enum Token {
    OpenBracket,
    CloseBracket,

    OpenParenthesis,
    CloseParenthesis,

    Comma,
    Colon,
    Range,
    
    Operator(Operator),

    String(Rc<str>),
    Integer(i32),
    Float(f32),
    Symbol(Rc<str>),

    Identifier(Rc<str>),
    Keyword(Keyword)
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
        #[from]
        err: ParseIntError,
    },

    #[error("failed to parse float")]
    FloatParse {
        #[from]
        err: ParseFloatError,
    },

    #[error("unexpected token \"{character}\"")]
    UnexpectedToken { character: char },
}

pub fn tokenize<T: AsRef<str>>(string: T) -> Result<Vec<Token>, TokenizeError> {
    let str_ref = string.as_ref();

    if str_ref.is_empty() {
        return Err(TokenizeError::EmptyExpression);
    }

    let mut chars = str_ref.chars().peekable();

    let mut tokens = vec![];

    'main_loop: while let Some(current) = chars.next() {
        match current {
            ' ' => {
                continue;
            }

            '[' => {
                tokens.push(Token::OpenBracket);
            }
            ']' => {
                tokens.push(Token::CloseBracket);
            }

            '(' => {
                tokens.push(Token::OpenParenthesis);
            }
            ')' => {
                tokens.push(Token::CloseParenthesis);
            }

            ',' => {
                tokens.push(Token::Comma);
            }
            ':' => {
                tokens.push(Token::Colon);
            }

            '>' => {
                if let Some(next) = chars.peek() {
                    if *next == '=' {
                        tokens.push(Token::Operator(Operator::GreaterOrEqual));
                        chars.next();
                        continue;
                    }
                }

                tokens.push(Token::Operator(Operator::Greater));
            }
            '<' => {
                if let Some(next) = chars.peek() {
                    if *next == '=' {
                        tokens.push(Token::Operator(Operator::SmallerOrEqual));
                        chars.next();
                        continue;
                    } else if *next == '>' {
                        tokens.push(Token::Operator(Operator::Inequality));
                        chars.next();
                        continue;
                    }
                }

                tokens.push(Token::Operator(Operator::Smaller));
            }

            '=' => {
                // if let Some(next) = chars.peek() {
                //     if *next == '=' {
                //         tokens.push(Token::Operator(Operator::Equality));
                //         chars.next();
                //         continue;
                //     }
                // }

                tokens.push(Token::Operator(Operator::AssignmentOrEquality));
            }

            '&' => {
                if let Some(next) = chars.peek() {
                    if *next == '&' {
                        tokens.push(Token::Operator(Operator::SpaceConcatenation));

                        chars.next();
                        continue;
                    }
                }

                tokens.push(Token::Operator(Operator::Concatenation));
            }

            '.' => {
                if let Some(next) = chars.peek() {
                    if *next == '.' {
                        chars.next();
                        tokens.push(Token::Range);
                        continue;
                    }
                }

                let mut buffer = String::with_capacity(2);
                buffer.push('.');

                while let Some(next) = chars.peek() {
                    if next.is_digit(10) {
                        buffer.push(*next);
                        chars.next();
                    }
                    else {
                        break;
                    }
                }

                if buffer.len() > 1 {
                    match buffer.parse::<f32>() {
                        Ok(number) => {
                            tokens.push(Token::Float(number));
                        }
                        Err(e) => {
                            return Err(TokenizeError::FloatParse { err: e });
                        }
                    }

                    continue;
                }

                tokens.push(Token::Operator(Operator::Dot));
            }

            '|' => {
                // if let Some(next) = chars.peek() {
                //     if *next == '|' {
                //         tokens.push(Token::Operator(Operator::Or));

                //         chars.next();
                //         continue;
                //     }
                // }

                return Err(TokenizeError::UnexpectedToken { character: '|' });
            }

            '+' => {
                tokens.push(Token::Operator(Operator::Addition));
            }
            '-' => {
                tokens.push(Token::Operator(Operator::Subtraction));
            }
            '*' => {
                tokens.push(Token::Operator(Operator::Multiplication));
            }
            '/' => {
                tokens.push(Token::Operator(Operator::Division));
            }

            '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' => {
                let mut buffer = String::with_capacity(1);
                let mut buffer2 = String::new();
                let mut buffer3 = String::new();

                let mut plusnegative = false;

                buffer.push(current);

                let mut is_float = false;

                while let Some(next) = chars.peek() {
                    if next.is_digit(10) {
                        if buffer3.is_empty() {
                            if is_float {
                                buffer2.push(*next);
                            } else {
                                buffer.push(*next);
                            }
                        } else {
                            buffer3.push(*next);
                        }

                        chars.next();
                    } else if *next == '.' {
                        if is_float {
                            if buffer2.is_empty() {
                                let combined = format!("{buffer}{buffer3}");

                                match combined.parse::<i32>() {
                                    Ok(number) => {
                                        tokens.push(Token::Integer(number));
                                    }
                                    Err(e) => {
                                        return Err(TokenizeError::IntParse { err: e });
                                    }
                                }

                                tokens.push(Token::Range);
                                chars.next();
                                buffer2.clear();
                                continue 'main_loop;
                            }

                            return Err(TokenizeError::DoubleDecimalPoint);
                        } else {
                            chars.next();
                            is_float = true;
                        }
                    } else if *next == 'e' {
                        if !buffer3.is_empty() {
                            return Err(TokenizeError::UnexpectedToken { character: *next });
                        }

                        buffer3.push(*next);

                        chars.next();
                    } else if buffer3.is_empty() && (*next == '-' || *next == '+') {
                        if plusnegative {
                            return Err(TokenizeError::UnexpectedToken { character: *next });
                        }

                        buffer3.push(*next);
                        chars.next();
                        plusnegative = true;
                    } else {
                        break;
                    }
                }

                let combined = if is_float {
                    format!("{buffer}.{buffer2}{buffer3}")
                } else {
                    format!("{buffer}{buffer3}")
                };

                if is_float {
                    match combined.parse::<f32>() {
                        Ok(number) => {
                            tokens.push(Token::Float(number));
                        }
                        Err(e) => {
                            return Err(TokenizeError::FloatParse { err: e });
                        }
                    }
                } else {
                    match combined.parse::<i32>() {
                        Ok(number) => {
                            tokens.push(Token::Integer(number));
                        }
                        Err(e) => {
                            return Err(TokenizeError::IntParse { err: e });
                        }
                    }
                }
            }

            '#' => {
                let mut buffer = String::with_capacity(1);

                while let Some(next) = chars.peek() {
                    if next.is_alphanumeric() || *next == '_' {
                        buffer.push(*next);
                        chars.next();
                    } else {
                        break;
                    }
                }

                if buffer.is_empty() {
                    return Err(TokenizeError::EmptyIdentifier);
                }

                tokens.push(Token::Symbol(buffer.into()));
            }

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
            }

            c => {
                let mut buffer = String::with_capacity(1);
                buffer.push(c);

                if !current.is_alphanumeric() && current != '_' {
                    return Err(TokenizeError::UnexpectedToken { character: current });
                }

                while let Some(next) = chars.peek() {
                    if next.is_alphanumeric() || *next == '_' {
                        buffer.push(*next);
                        chars.next();
                    } else {
                        break;
                    }
                }

                match buffer.deref() {
                    "void" => {
                        tokens.push(Token::Keyword(Keyword::Void));
                    },

                    "contains" => {
                        tokens.push(Token::Operator(Operator::Contains));
                    },

                    "starts" => {
                        tokens.push(Token::Operator(Operator::Starts));
                    },

                    "and" => {
                        tokens.push(Token::Operator(Operator::And));
                    },

                    "or" => {
                        tokens.push(Token::Operator(Operator::Or));
                    },

                    "not" => {
                        tokens.push(Token::Operator(Operator::Not));
                    },

                    _ => {
                        tokens.push(Token::Identifier(buffer.into()))
                    }
                }
            }
        }
    }

    Ok(tokens)
}
