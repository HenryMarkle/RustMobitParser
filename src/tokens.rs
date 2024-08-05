use log::error;
use std::{
    num::{ParseFloatError, ParseIntError}, ops::Deref, rc::Rc
};
use thiserror;

#[derive(Debug, Clone, PartialEq)]
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

#[derive(Debug, PartialEq)]
pub enum Keyword {
    Global,
    Property,
    Case,
    Otherwise,
    Repeat,
    While,
    With,
    Within,
    Word,
    Down,
    In,
    Of,
    On,
    Void,
    If,
    Then,
    Else,
    End,
    Exit,
    Item,
    To,
    Before,
    After,
    Into,
    Put,
    Loop,
    Menu,
    Next,
    Return,
    Set,
    Sprite,
    Intersects,
    Char,
    Line,
    The,

    INF,
    NAN
}

#[derive(Debug, PartialEq)]
pub enum Token {
    OpenBracket,
    CloseBracket,

    OpenParenthesis,
    CloseParenthesis,

    Comma,
    Colon,
    Range,

    NewLine,
    
    Operator(Operator),

    String(Rc<str>),
    Integer(i32),
    Float(f32),
    Symbol(Rc<str>),
    Path(Rc<[Box<str>]>),

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
            ' ' | '\t' => {
                continue;
            },
            

            '\\' => {
                if let Some(next) = chars.peek() {
                    if *next == '\n' {
                        chars.next();
                    } else if *next == '\r' {
                        chars.next();

                        if let Some(next) = chars.peek() {
                            if *next == '\n' {
                                chars.next();
                            }
                        }
                    }
                }
            }

            '\n' | '\r' => {
                if current == '\r' {
                    if let Some(next) = chars.peek() {
                        if *next == '\n' {
                            chars.next();
                        }
                    }
                }

                chars.next();

                tokens.push(Token::NewLine);
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
                    "global" => {
                        tokens.push(Token::Keyword(Keyword::Void));
                    },
                    
                    "property" => {
                        tokens.push(Token::Keyword(Keyword::Void));
                    },
                    
                    "void" => {
                        tokens.push(Token::Keyword(Keyword::Void));
                    },

                    "if" => {
                        tokens.push(Token::Keyword(Keyword::If));
                    },

                    "then" => {
                        tokens.push(Token::Keyword(Keyword::Then));
                    },

                    "else" => {
                        tokens.push(Token::Keyword(Keyword::Else));
                    },

                    "case" => {
                        tokens.push(Token::Keyword(Keyword::Case));
                    },
                    
                    "repeat" => {
                        tokens.push(Token::Keyword(Keyword::Repeat));
                    },
                    
                    "while" => {
                        tokens.push(Token::Keyword(Keyword::While));
                    },
                    
                    "with" => {
                        tokens.push(Token::Keyword(Keyword::With));
                    },

                    "of" => {
                        tokens.push(Token::Keyword(Keyword::Of));
                    },

                    "end" => {
                        tokens.push(Token::Keyword(Keyword::End));
                    },

                    "exit" => {
                        tokens.push(Token::Keyword(Keyword::Exit));
                    },

                    "loop" => {
                        tokens.push(Token::Keyword(Keyword::Loop));
                    },

                    "char" => {
                        tokens.push(Token::Keyword(Keyword::Char));
                    },

                    "item" => {
                        tokens.push(Token::Keyword(Keyword::Item));
                    },

                    "to" => {
                        tokens.push(Token::Keyword(Keyword::To));
                    },
                    
                    "into" => {
                        tokens.push(Token::Keyword(Keyword::Into));
                    },

                    "word" => {
                        tokens.push(Token::Keyword(Keyword::Word));
                    },

                    "before" => {
                        tokens.push(Token::Keyword(Keyword::Before));
                    },

                    "after" => {
                        tokens.push(Token::Keyword(Keyword::After));
                    },
                    
                    "the" => {
                        tokens.push(Token::Keyword(Keyword::The));
                    },
                    
                    "within" => {
                        tokens.push(Token::Keyword(Keyword::Within));
                    },
                    
                    "in" => {
                        tokens.push(Token::Keyword(Keyword::In));
                    },

                    "put" => {
                        tokens.push(Token::Keyword(Keyword::Put));
                    },
                    
                    "menu" => {
                        tokens.push(Token::Keyword(Keyword::Menu));
                    },
                    
                    "next" => {
                        tokens.push(Token::Keyword(Keyword::Next));
                    },
                    
                    "sprite" => {
                        tokens.push(Token::Keyword(Keyword::Next));
                    },
                    
                    "intersects" => {
                        tokens.push(Token::Keyword(Keyword::Next));
                    },
                    
                    "down" => {
                        tokens.push(Token::Keyword(Keyword::Down));
                    },
                    
                    "otherwise" => {
                        tokens.push(Token::Keyword(Keyword::Otherwise));
                    },

                    "return" => {
                        tokens.push(Token::Keyword(Keyword::Return));
                    },
                    
                    "set" => {
                        tokens.push(Token::Keyword(Keyword::Set));
                    },
                    
                    "line" => {
                        tokens.push(Token::Keyword(Keyword::Line));
                    },

                    "INT" => {
                        tokens.push(Token::Keyword(Keyword::INF));
                    },
                    
                    "NAN" => {
                        tokens.push(Token::Keyword(Keyword::INF));
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
