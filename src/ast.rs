use std::{
    collections::HashMap,
    rc::Rc
};
use std::fmt::{Display, Formatter};
use crate::tokens::{self, Operator, Token};
use thiserror;
use log::{debug, error};

#[derive(Debug)]
pub enum BinaryOperator {
    And,
    Or,

    Addition,
    Subtraction,
    Multiplication,
    Division,
    Mod,

    Greater,
    Smaller,
    GreaterOrEqual,
    SmallerOrEqual,

    Equal,
    NotEqual,

    Contains,
    Starts,

    Concatenation,
    SpaceConcatenation
}

#[derive(Debug)]
pub enum UnaryOperator {
    Negate,
    Negative,
    Positive
}

#[derive(Debug)]
pub enum PostOperator {
    FunctionCall(Box<[Expression]>),

    MemberAccess(Rc<str>),

    Slice {
        begin: Box<Expression>,
        end: Box<Expression>
    },

    Index(Box<Expression>)
}

#[derive(Debug)]
pub enum Expression {
    String(Rc<str>),
    Symbol(Rc<str>),
    Integer(i32),
    Float(f32),

    LinearList(Box<[Expression]>),
    PropertyList(HashMap<Rc<str>, Expression>),

    Identifier(Rc<str>),

    BinaryOperation {
        operator: BinaryOperator,
        left: Box<Expression>,
        right: Box<Expression>
    },

    UnaryOperation {
        operator: UnaryOperator,
        right: Box<Expression>
    },

    PostOperation {
        left: Box<Expression>,
        operator: PostOperator
    },

    Void
}

#[derive(Debug)]
pub struct SwitchCase {
    pub case: Box<[Expression]>,
    pub block: Box<[Instruction]>
}

#[derive(Debug)]
pub enum Instruction {
    Assignment {
        identifier: Rc<str>,
        expression: Box<Expression>
    },

    Conditional {
        condition: Box<Expression>,

        positive: Box<[Instruction]>,
        negative: Box<[Instruction]>
    },

    Switch {
        condition: Box<Expression>,
        cases: Box<[SwitchCase]>
    },

    GlobalCall {
        name: Rc<str>,
        args: Box<[Expression]>
    }
}

impl TryFrom<&tokens::Operator> for BinaryOperator {
    type Error = ();

    fn try_from(value: &tokens::Operator) -> Result<Self, Self::Error> {
        use BinaryOperator::*;

        match value {
            tokens::Operator::Concatenation => Ok(Concatenation),
            tokens::Operator::SpaceConcatenation => Ok(SpaceConcatenation),

            tokens::Operator::Or => Ok(Or),
            tokens::Operator::And => Ok(And),

            tokens::Operator::Addition => Ok(Addition),
            tokens::Operator::Subtraction => Ok(Subtraction),
            tokens::Operator::Multiplication => Ok(Multiplication),
            tokens::Operator::Division => Ok(Division),
            tokens::Operator::Mod => Ok(Mod),

            tokens::Operator::Inequality => Ok(NotEqual),

            tokens::Operator::Contains => Ok(Contains),

            tokens::Operator::Greater => Ok(Greater),
            tokens::Operator::Smaller => Ok(Smaller),
            tokens::Operator::GreaterOrEqual => Ok(GreaterOrEqual),
            tokens::Operator::SmallerOrEqual => Ok(SmallerOrEqual),
            tokens::Operator::AssignmentOrEquality => Ok(Equal),

            _ => Err(())
        }
    }
}

impl TryFrom<tokens::Operator> for BinaryOperator {
    type Error = ();

    fn try_from(value: tokens::Operator) -> Result<Self, Self::Error> {
        Self::try_from(&value)
    }
}

impl TryFrom<&tokens::Operator> for UnaryOperator {
    type Error = ();

    fn try_from(value: &tokens::Operator) -> Result<Self, Self::Error> {
        match value {
            Operator::Not => Ok(UnaryOperator::Negate),
            Operator::Addition => Ok(UnaryOperator::Positive),
            Operator::Subtraction => Ok(UnaryOperator::Negative),

            _ => Err(())
        }
    }
}

impl Display for BinaryOperator {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", match self {
            BinaryOperator::And => "and",
            BinaryOperator::Or => "or",
            BinaryOperator::Addition => "+",
            BinaryOperator::Subtraction => "-",
            BinaryOperator::Multiplication => "*",
            BinaryOperator::Division => "/",
            BinaryOperator::Greater => ">",
            BinaryOperator::Smaller => "<",
            BinaryOperator::GreaterOrEqual => ">=",
            BinaryOperator::SmallerOrEqual => "<=",
            BinaryOperator::Contains => "contains",
            BinaryOperator::Starts => "starts",
            BinaryOperator::Concatenation => "&",
            BinaryOperator::SpaceConcatenation => "&&",
            BinaryOperator::Mod => "mod",
            BinaryOperator::Equal => "=",
            BinaryOperator::NotEqual => "<>",
        })
    }
}

impl Display for UnaryOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", match self {
            UnaryOperator::Negate => "not",
            UnaryOperator::Negative => "-",
            UnaryOperator::Positive => "+",
        })
    }
}

impl Display for PostOperator {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            PostOperator::FunctionCall(args) => {
                let args_vec: Vec<String> = args.iter()
                    .map(|a| format!("{:?}", a))
                    .collect();

                write!(f, "({})", args_vec.join(", "))
            },

            PostOperator::MemberAccess(name) => {
                write!(f, ".{}", name)
            },

            PostOperator::Slice { begin, end } => {
                write!(f, "[{:?}..{:?}]", begin, end)
            },

            PostOperator::Index(index) => {
                write!(f, "[{:?}]", index)
            },
        }
    }
}

fn op_precedence(op: &tokens::Operator) -> u8 {
    match op {
        tokens::Operator::Dot => 6,
        tokens::Operator::Contains => 1,
        tokens::Operator::Starts => 1,
        tokens::Operator::Concatenation => 2,
        tokens::Operator::SpaceConcatenation => 2,
        tokens::Operator::Or => 4,
        tokens::Operator::And => 4,
        tokens::Operator::Addition => 3,
        tokens::Operator::Subtraction => 3,
        tokens::Operator::Multiplication => 4,
        tokens::Operator::Division => 4,
        tokens::Operator::Mod => 4,
        tokens::Operator::Inequality => 1,
        tokens::Operator::Greater => 1,
        tokens::Operator::Smaller => 1,
        tokens::Operator::GreaterOrEqual => 1,
        tokens::Operator::SmallerOrEqual => 1,
        tokens::Operator::AssignmentOrEquality => 0,
        tokens::Operator::Not => 5
    }
}

#[derive(Debug, thiserror::Error)]
pub enum TokensParseError {
    #[error("unexpected concatenation operator")]
    UnexpectedConcatenationOperator,

    #[error("unexpected operator")]
    UnexpectedOperator(tokens::Operator),

    #[error("unexpected token: {:?}", character)]
    UnexpectedToken { character: String },

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

    #[error("unsatisfied inequality operator")]
    UnsatisfiedConcatenationOperator,    

    #[error("undefined constant \"{}\"", constant)]
    UndefinedConstant { constant: String }
}

fn parse_tokens_helper(tokens: &[Token], cursor: usize, min_precedence: u8) -> Result<(Expression, usize), TokensParseError> {
    debug!("recursive call (min_prec: {})", min_precedence);

    if tokens.is_empty() { return Err(TokensParseError::EmptyTokens); }

    let length = tokens.len();

    let mut begin = cursor;

    if begin >= length { return Err(TokensParseError::OutOfRange); }

    let current = &tokens[begin];

    let mut parse_res: Result<_, _> = Err(TokensParseError::EmptyTokens);
    match current {
        Token::OpenBracket => {
            debug!("parsing a collection at ({})", begin);

            let mut sub_nodes = vec![];
            let mut map = HashMap::new();
            let mut commad = true;
            let mut is_prop = false;
            begin += 1;

            'collection_loop: while begin < length {
                match &tokens[begin] {

                    Token::CloseBracket => {
                        // are trailing commas allowed?
                        if commad && if is_prop { !map.is_empty() } else { !sub_nodes.is_empty() } {
                            error!("unexpected trailing comma at ({})", begin);
                            return Err(TokensParseError::UnexpectedToken { character: format!("{:?}", Token::Comma) });
                        }

                        if is_prop {
                            debug!("done parsing property list at ({})", begin);
                            parse_res = Ok((Expression::PropertyList(map), begin));
                            break 'collection_loop;
                        }

                        debug!("done parsing linear list at ({})", begin);
                        parse_res = Ok((Expression::LinearList(sub_nodes.into()), begin));
                        break 'collection_loop;
                    },

                    Token::Colon => {
                        if begin == cursor + 1 {
                            is_prop = true;
                        } else if !is_prop {
                            error!("found an illegal colon at ({})", begin);
                            return Err(TokensParseError::UnexpectedToken { character: format!("{:?}", Token::Comma) });
                        }
                    },

                    Token::Symbol(key) => {
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
                            Token::Comma | Token::Symbol(_) => {
                                error!("illegal token for a property value at ({})", begin);
                                return Err(TokensParseError::UnexpectedToken { character: "".into() });
                            },

                            _ => {
                                debug!("parsing a property value sub-expression at ({})", value_pos);
                                let (node, reached) = parse_tokens_helper(&tokens, value_pos, 0)?;

                                map.insert(Rc::clone(key), node);
                                begin = reached;
                                debug!("parsing property value sub-expression done at ({})", begin);

                            }
                        }
                    },

                    Token::Comma => {
                        if commad {
                            error!("double comma at ({})", begin);
                            return Err(TokensParseError::UnexpectedToken { character: format!("{:?}", Token::Comma) });
                        }
                        commad = true;
                    },

                    t => {
                        if !commad {
                            error!("expected a comma but instead got ({:?}) at ({})", t, begin);
                            return Err(TokensParseError::ExpectedToken { character: ',' });
                        }

                        commad = false;

                        if is_prop {
                            error!("found a linear list item while parsing a property list at ({})", begin);
                            return Err(TokensParseError::ObscureCollectionType);
                        }

                        debug!("parsing a linear list sub-expression at ({})", begin);
                        let (node, reached) = parse_tokens_helper(&tokens, begin, 0)?;

                        sub_nodes.push(node);
                        begin = reached;
                        debug!("parsing linear list sub-expression done at ({})", begin);
                    }
                };

                begin += 1;
            };

            if parse_res.is_err() {
                error!("expected the collection to end but it didn't");
                return Err(TokensParseError::ImbalancedCollection);
            }
        },

        Token::Operator(op) => {
            let uop = UnaryOperator::try_from(op)
                .map_err(|_| TokensParseError::UnexpectedToken { character: format!("{:?}", op) })?;

            if begin + 1 >= length {
                return Err(TokensParseError::UnexpectedEnd);
            }

            let (parsed, reached) = parse_tokens_helper(
                tokens,
                begin + 1,
                5
            )?;

            parse_res = Ok(
                (
                    Expression::UnaryOperation {
                        operator: uop,
                        right: Box::new(parsed)
                    },

                    reached
                ));
        },
        Token::String(string) => {
            debug!("parsing a string at ({})", begin);

            parse_res = Ok((Expression::String(Rc::clone(string)), begin));
        },
        Token::Integer(int) => {
            debug!("parsing an integer at ({})", begin);
            parse_res = Ok((Expression::Integer(*int), begin));
        },
        Token::Float(float) => {
            debug!("parsing a float at ({})", begin);
            parse_res = Ok((Expression::Float(*float), begin))
        },

        Token::OpenParenthesis => {
            // (<expression>)

            if begin + 1 >= length {
                error!("expected an expression or ')' at ({})", begin + 1);
                return Err(TokensParseError::UnexpectedEnd);
            }

            debug!("parsing parenthesis sub-expression at ({})", begin + 1);

            let (parsed_expr, reached) = parse_tokens_helper(
                &tokens,
                begin + 1,
                0
            )?;

            if reached + 1 >= length {
                error!("expected ')' at ({})", reached + 1);
                return Err(TokensParseError::UnexpectedEnd);
            }

            match &tokens[reached + 1] {
                Token::CloseParenthesis => {
                    begin = reached + 1;
                    parse_res = Ok((parsed_expr, begin));
                },

                t => {
                    error!("unexpected token ({:?}) at ({})", t, reached + 1);
                    return Err(TokensParseError::UnexpectedToken { character: format!("{:?}", t)});
                }
            }
        },


        Token::Comma => {
            error!("unexpected token at ({})", begin);
            return Err(TokensParseError::UnexpectedToken { character: format!("{:?}", Token::Comma) });
        },
        Token::Colon => {
            error!("unexpected token at ({})", begin);
            return Err(TokensParseError::UnexpectedToken { character: format!("{:?}", Token::Colon) });
        },
        Token::CloseBracket => {
            error!("unexpected token at ({})", begin);
            return Err(TokensParseError::UnexpectedToken { character: format!("{:?}", Token::CloseBracket) });
        },
        Token::CloseParenthesis => {
            error!("unexpected token at ({})", begin);
            return Err(TokensParseError::UnexpectedToken { character: format!("{:?}", Token::CloseParenthesis) });
        },
        Token::Symbol(m) => {
            debug!("parsing symbol at ({})", begin);
            parse_res = Ok(
                (
                    Expression::Symbol(Rc::clone(m)),
                    begin
                )
            );
        },
        Token::Range => {
            error!("unexpected range token at ({})", begin);
            return Err(TokensParseError::UnexpectedToken { character: "..".into() });
        },

        Token::Identifier(i) => {
            debug!("parsing an identifier at ({})", begin);
            parse_res = Ok((Expression::Identifier(Rc::clone(i)), begin));
        }

        Token::Keyword(k) => {
            return Err(TokensParseError::UnexpectedToken { character: format!("{:?}", k) });
        }
    }

    let (parsed, reached) = parse_res.unwrap();
    begin = reached;
    let mut subtree = parsed;

    'op_loop: while begin + 1 < length {

        match &tokens[begin + 1] {
            // function call
            Token::OpenParenthesis => {
                debug!("parsing function arguments at ({})", begin + 1);

                let mut commad = true;
                let mut next = begin + 2;

                let mut args = vec![];

                while next < length {
                    match &tokens[next] {
                        Token::CloseParenthesis => {
                            if commad {
                                debug!("unexpected trailing comma at ({})", next);
                                return Err(TokensParseError:: UnexpectedToken { character: ",".into() });
                            }

                            let new_subtree = Expression::PostOperation {
                                operator: PostOperator::FunctionCall(args.into()),
                                left: Box::new(subtree)
                            };

                            subtree = new_subtree;
                            begin = next;

                            continue 'op_loop;
                        },

                        Token::Comma => {
                            if commad {
                                debug!("unexpected comma at ({})", next);
                                return Err(TokensParseError::UnexpectedToken { character: ",".into() });
                            }

                            commad = true;
                            next += 1;
                        },

                        _ => {
                            if !commad {
                                debug!("expected a comma at ({})", next);
                                return Err(TokensParseError::ExpectedToken { character: ',' });
                            }

                            debug!("parsing function argument #{} at ({})", args.len() + 1, next);

                            let (parsed, reached) = parse_tokens_helper(
                                tokens,
                                next,
                                0
                            )?;

                            next = reached + 1;
                            args.push(parsed);
                            commad = false;
                        }
                    }
                }
            },

            // indexing and slicing
            Token::OpenBracket => {
                if begin + 2 >= length {
                    return Err(TokensParseError::UnexpectedEnd);
                }

                let (parsed_in, reached) = parse_tokens_helper(
                    tokens,
                    begin + 2,
                    0
                )?;

                match &tokens[reached + 1] {
                    Token::Range => {
                        debug!("parsing a range at ({})", reached + 1);

                        if reached + 2 >= length {
                            return Err(TokensParseError::UnexpectedEnd);
                        }

                        let (parsed_end, end_reached) = parse_tokens_helper(
                            tokens,
                            reached + 2,
                            0
                        )?;

                        match &tokens[end_reached + 1] {
                            Token::CloseBracket => {
                                let new_subtree = Expression::PostOperation {
                                    operator: PostOperator::Slice {
                                        begin: Box::new(parsed_in),
                                        end: Box::new(parsed_end)
                                    },

                                    left: Box::new(subtree)
                                };

                                subtree = new_subtree;
                                begin = end_reached + 1;
                            },

                            t => {
                                return Err(TokensParseError::UnexpectedToken {
                                    character: format!("{:?}", t)
                                })
                            }
                        }
                    },

                    Token::CloseBracket => {
                        debug!("parsed an indexing operator. ends at ({})", reached + 1);
                        let new_subtree = Expression::PostOperation {
                            operator: PostOperator::Index(Box::new(parsed_in)),
                            left: Box::new(subtree)
                        };

                        subtree = new_subtree;
                        begin = reached + 1;
                    },

                    t => {
                        return Err(TokensParseError::UnexpectedToken {
                            character: format!("{:?}", t)
                        });
                    }
                }
            },

            Token::Operator(op) => {
                debug!("found an operator ({:?}) at ({})", op, begin + 1);

                // looking for member access operator
                match op {
                    tokens::Operator::Dot => {

                        match &tokens[begin + 2] {
                            Token::Identifier(identifier) => {
                                let new_subtree = Expression::PostOperation {
                                    operator: PostOperator::MemberAccess(Rc::clone(identifier)),
                                    left: Box::new(subtree)
                                };

                                begin += 2;
                                subtree = new_subtree;

                                continue 'op_loop;
                            },

                            t => {
                                return Err(
                                    TokensParseError::UnexpectedToken {
                                        character: format!("{:?}", &t)
                                    }
                                );
                            }
                        }
                    },

                    _ => ()
                }
                //

                let precedence = op_precedence(op);

                let bop = BinaryOperator::try_from(op)
                    .map_err(|_| TokensParseError::UnexpectedToken {
                        character: format!("{:?}", op.clone())
                    })?;

                if precedence < min_precedence {
                    break 'op_loop;
                }

                debug!("parsing the right side of the operator at ({})", begin + 2);

                let (right, right_reached) = parse_tokens_helper(
                    tokens,
                    begin + 2,
                    precedence + 1
                )?;

                let new_subtree = Expression::BinaryOperation {
                    operator: bop,
                    left: Box::new(subtree),
                    right: Box::new(right)
                };

                subtree = new_subtree;
                begin = right_reached;
            },

            _ => break 'op_loop
        }
    }


    Ok((subtree, begin))
}

pub fn parse_tokens<T : AsRef<[Token]>>(tokens: T) -> Result<Expression, TokensParseError> {
    match parse_tokens_helper(tokens.as_ref(), 0, 0) {
        Ok((node, _)) => Ok(node),
        Err(e) => Err(e)
    }
}
