use std::{
    collections::HashMap,
    rc::Rc
};
use std::fmt::{Display, Formatter};
use crate::tokens::{self, Operator, Token, Keyword};
use thiserror;
use log::{debug, error, trace};


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
    Path(Rc<[Box<str>]>),

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
    pub block: Box<[Statement]>
}

#[derive(Debug)]
pub enum ElseConditionalBlock {
    Else(Box<[Statement]>),
    ElseIf(Box<ConditionalBlock>)
}

#[derive(Debug)]
pub struct ConditionalBlock {
    condition: Box<Expression>,

    block: Box<[Statement]>,
    else_block: Option<ElseConditionalBlock>
}

#[derive(Debug)]
pub enum Statement {
    Assignment {
        assignee: Box<Expression>,
        specified_type: Option<Rc<str>>,
        expression: Box<Expression>
    },

    Condition(ConditionalBlock),

    Switch {
        condition: Box<Expression>,
        cases: Box<[SwitchCase]>
    },

    Expression(Expression),

    PutInto,
    Exit,
    Global,
    TypeSpec,
    Repeat,

    Return
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
pub enum ExpressionParseError {
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

#[derive(Debug, thiserror::Error)]
pub enum AssignmentParseError {
    #[error("unexpected end")]
    UnexpectedEnd,

    #[error("failed to parse assignment's right-side expression")]
    Expression(#[from] ExpressionParseError),

    #[error("invalid assignment operator")]
    InvalidOperator,

    #[error("invalid type identifier")]
    InvalidTypeIdentifier,

    #[error("unexpected token")]
    UnexpectedToken(String)
}


#[derive(Debug, thiserror::Error)]
pub enum StatementParseError {
    #[error("unexpected end")]
    UnexpectedEnd,

    #[error("unexpected token")]
    UnexpectedToken(String),

    #[error("failed to parse condition")]
    ConditionalParseError(#[from] ConditionalBlockParseError),
    
    #[error("failed to parse assignment")]
    Assignment(#[from] AssignmentParseError)
}

#[derive(Debug, thiserror::Error)]
pub enum ConditionalBlockParseError {
    #[error("unexpected end")]
    UnexpectedEnd,

    #[error("unexpected token")]
    UnexpectedToken(String),

    #[error("failed to parse conditional expression")]
    ExpressionParseError(#[from] ExpressionParseError),

    #[error("failed to parse a statement")]
    StatementParseError(String)
}

#[derive(Debug, thiserror::Error)]
pub enum ParseError {

    #[error("failed to parse expression")]
    Expression(#[from] ExpressionParseError),

    #[error("failed to parse statement")]
    Statement(#[from] StatementParseError),

    #[error("failed to parse conditition")]
    Condition(#[from] ConditionalBlockParseError)
}

fn parse_expression(tokens: &[Token], cursor: usize, min_precedence: u8, equals: bool) -> Result<(Expression, usize), ExpressionParseError> {
    debug!("recursive call (min_prec: {})", min_precedence);

    if tokens.is_empty() { return Err(ExpressionParseError::EmptyTokens); }

    let length = tokens.len();

    let mut begin = cursor;

    if begin >= length { return Err(ExpressionParseError::OutOfRange); }

    let current = &tokens[begin];

    let mut parse_res: Result<_, _> = Err(ExpressionParseError::EmptyTokens);
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
                            return Err(ExpressionParseError::UnexpectedToken { character: format!("{:?}", Token::Comma) });
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
                            return Err(ExpressionParseError::UnexpectedToken { character: format!("{:?}", Token::Comma) });
                        }
                    },

                    Token::Symbol(key) => {
                        debug!("parsing an identifier at ({})", begin);

                        if !commad {
                            error!("expected a comma at ({})", begin);
                            return Err(ExpressionParseError::ExpectedToken { character: ',' });
                        }
                        commad = false;

                        if !is_prop {
                            if !sub_nodes.is_empty() {
                                error!("found a property key while parsing a linear list at ({})", begin);
                                return Err(ExpressionParseError::ObscureCollectionType);
                            }

                            debug!("collection is a property list at ({})", begin);
                            is_prop = true;
                        }

                        let colon_pos = begin + 1;
                        let value_pos = colon_pos + 1;

                        if value_pos >= length { return Err(ExpressionParseError::UnexpectedEnd); }

                        match &tokens[colon_pos] {
                            Token::Colon => (),
                            _ => {
                                error!("property key wasn't followed by a colon at ({})", begin);
                                return Err(ExpressionParseError::ExpectedToken { character: ':' });
                            }
                        }

                        debug!("checking property value at ({})", begin);

                        match &tokens[value_pos] {
                            Token::CloseBracket | Token::CloseParenthesis | Token::Colon |
                            Token::Comma | Token::Symbol(_) => {
                                error!("illegal token for a property value at ({})", begin);
                                return Err(ExpressionParseError::UnexpectedToken { character: "".into() });
                            },

                            _ => {
                                debug!("parsing a property value sub-expression at ({})", value_pos);
                                let (node, reached) = parse_expression(&tokens, value_pos, 0, equals)?;

                                map.insert(Rc::clone(key), node);
                                begin = reached;
                                debug!("parsing property value sub-expression done at ({})", begin);

                            }
                        }
                    },

                    Token::Comma => {
                        if commad {
                            error!("double comma at ({})", begin);
                            return Err(ExpressionParseError::UnexpectedToken { character: format!("{:?}", Token::Comma) });
                        }
                        commad = true;
                    },

                    t => {
                        if !commad {
                            error!("expected a comma but instead got ({:?}) at ({})", t, begin);
                            return Err(ExpressionParseError::ExpectedToken { character: ',' });
                        }

                        commad = false;

                        if is_prop {
                            error!("found a linear list item while parsing a property list at ({})", begin);
                            return Err(ExpressionParseError::ObscureCollectionType);
                        }

                        debug!("parsing a linear list sub-expression at ({})", begin);
                        let (node, reached) = parse_expression(&tokens, begin, 0, equals)?;

                        sub_nodes.push(node);
                        begin = reached;
                        debug!("parsing linear list sub-expression done at ({})", begin);
                    }
                };

                begin += 1;
            };

            if parse_res.is_err() {
                error!("expected the collection to end but it didn't");
                return Err(ExpressionParseError::ImbalancedCollection);
            }
        },

        Token::Operator(op) => {
            let uop = UnaryOperator::try_from(op)
                .map_err(|_| ExpressionParseError::UnexpectedToken { character: format!("{:?}", op) })?;

            if begin + 1 >= length {
                return Err(ExpressionParseError::UnexpectedEnd);
            }

            let (parsed, reached) = parse_expression(
                tokens,
                begin + 1,
                5, 
                equals
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
        Token::Path(p) => {
            debug!("parsing a path at ({})", begin);
            parse_res = Ok(
                (
                    Expression::Path(Rc::clone(p)),
                    begin
                )
            );
        }

        Token::OpenParenthesis => {
            // (<expression>)

            if begin + 1 >= length {
                error!("expected an expression or ')' at ({})", begin + 1);
                return Err(ExpressionParseError::UnexpectedEnd);
            }

            debug!("parsing parenthesis sub-expression at ({})", begin + 1);

            let (parsed_expr, reached) = parse_expression(
                &tokens,
                begin + 1,
                0, 
                equals
            )?;

            if reached + 1 >= length {
                error!("expected ')' at ({})", reached + 1);
                return Err(ExpressionParseError::UnexpectedEnd);
            }

            match &tokens[reached + 1] {
                Token::CloseParenthesis => {
                    begin = reached + 1;
                    parse_res = Ok((parsed_expr, begin));
                },

                t => {
                    error!("unexpected token ({:?}) at ({})", t, reached + 1);
                    return Err(ExpressionParseError::UnexpectedToken { character: format!("{:?}", t)});
                }
            }
        },


        Token::Comma => {
            error!("unexpected token at ({})", begin);
            return Err(ExpressionParseError::UnexpectedToken { character: format!("{:?}", Token::Comma) });
        },
        Token::Colon => {
            error!("unexpected token at ({})", begin);
            return Err(ExpressionParseError::UnexpectedToken { character: format!("{:?}", Token::Colon) });
        },
        Token::CloseBracket => {
            error!("unexpected token at ({})", begin);
            return Err(ExpressionParseError::UnexpectedToken { character: format!("{:?}", Token::CloseBracket) });
        },
        Token::CloseParenthesis => {
            error!("unexpected token at ({})", begin);
            return Err(ExpressionParseError::UnexpectedToken { character: format!("{:?}", Token::CloseParenthesis) });
        },

        Token::NewLine => {
            error!("unexpected new line at ({})", begin);
            return Err(ExpressionParseError::UnexpectedToken { character: format!("\"\"") });
        },

        Token::BackSlash => {
            error!("unexpected new line at ({})", begin);
            return Err(ExpressionParseError::UnexpectedToken { character: format!("\\") });
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
            return Err(ExpressionParseError::UnexpectedToken { character: "..".into() });
        },

        Token::Identifier(i) => {
            debug!("parsing an identifier at ({})", begin);
            parse_res = Ok((Expression::Identifier(Rc::clone(i)), begin));
        }

        Token::Keyword(k) => {
            return Err(ExpressionParseError::UnexpectedToken { character: format!("{:?}", k) });
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
                                return Err(ExpressionParseError:: UnexpectedToken { character: ",".into() });
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
                                return Err(ExpressionParseError::UnexpectedToken { character: ",".into() });
                            }

                            commad = true;
                            next += 1;
                        },

                        _ => {
                            if !commad {
                                debug!("expected a comma at ({})", next);
                                return Err(ExpressionParseError::ExpectedToken { character: ',' });
                            }

                            debug!("parsing function argument #{} at ({})", args.len() + 1, next);

                            let (parsed, reached) = parse_expression(
                                tokens,
                                next,
                                0, 
                                equals
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
                    return Err(ExpressionParseError::UnexpectedEnd);
                }

                let (parsed_in, reached) = parse_expression(
                    tokens,
                    begin + 2,
                    0, 
                    equals
                )?;

                match &tokens[reached + 1] {
                    Token::Range => {
                        debug!("parsing a range at ({})", reached + 1);

                        if reached + 2 >= length {
                            return Err(ExpressionParseError::UnexpectedEnd);
                        }

                        let (parsed_end, end_reached) = parse_expression(
                            tokens,
                            reached + 2,
                            0, 
                            equals
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
                                return Err(ExpressionParseError::UnexpectedToken {
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
                        return Err(ExpressionParseError::UnexpectedToken {
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
                                    ExpressionParseError::UnexpectedToken {
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
                    .map_err(|_| ExpressionParseError::UnexpectedToken {
                        character: format!("{:?}", op.clone())
                    })?;

                match op {
                    Operator::AssignmentOrEquality => {
                        if equals {
                            return Ok(
                                (
                                    subtree,
                                    begin
                                )
                            )
                        }
                    },

                    _ => {

                    }
                }

                if precedence < min_precedence {
                    break 'op_loop;
                }

                debug!("parsing the right side of the operator at ({})", begin + 2);

                let (right, right_reached) = parse_expression(
                    tokens,
                    begin + 2,
                    precedence + 1, 
                    equals
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


pub fn parse_statement(tokens: &[Token], cursor: usize) -> Result<(Statement, usize), StatementParseError> {
    debug!("parsing a statement at ({})", cursor);
    
    if cursor >= tokens.len() {
        error!("unexpected end of tokens");
        return Err(StatementParseError::UnexpectedEnd);
    }
    
    match &tokens[cursor] {
        Token::Keyword(k) => match k {
            Keyword::If => {
                let (parsed_if, reached) = parse_condition(tokens, cursor)?;

                return Ok(
                    (
                        Statement::Condition(parsed_if),
                        reached
                    )
                )
            },

            wk => {
                error!("unexpected keyword at ({})", cursor);
                return Err(StatementParseError::UnexpectedToken(format!("{:?}", wk)));
            }
        },

        wt => {
            error!("unexpected token at ({})", cursor);
            return Err(StatementParseError::UnexpectedToken(format!("{:?}", wt)));
        }
    }
}

fn parse_assignment(tokens: &[Token], cursor: usize) -> Result<(Statement, usize), AssignmentParseError> {
    debug!("parsing assignment at ({})", cursor);
    
    if cursor >= tokens.len() {
        error!("unexpected end of tokens at ({})", cursor);
        return Err(AssignmentParseError::UnexpectedEnd);
    }

    let (expr_parsed, reached) = parse_expression(tokens, cursor, 0, false)?;

    let mut next = reached + 1;

    if next >= tokens.len() {
        error!("unexpected end of tokens at ({}). expected ':' or '='", next);
        return Err(AssignmentParseError::UnexpectedEnd);
    }

    match &tokens[next] {
        Token::Colon => {
            next += 1;

            if next >= tokens.len() {
                error!("unexpected end of tokens at ({}). expected a type identifier", next);
                trace!("<assignee>: >token<");
                return Err(AssignmentParseError::UnexpectedEnd);
            }

            let (type_id, reached) = parse_expression(tokens, next, 0, false)?;

            match type_id {
                Expression::Identifier(id) => {
                    next = reached + 1;

                    if next >= tokens.len() {
                        error!("unexpected end of tokens at ({}). expected '='", next);
                        trace!("<assignee>: <type_id> >token<");
                        return Err(AssignmentParseError::UnexpectedEnd);
                    }

                    match &tokens[next] {
                        Token::Operator(op) => match op {
                            Operator::AssignmentOrEquality => {
                                next += 1;

                                if next >= tokens.len() {
                                    error!("unexpected end of tokens at ({}). expected an expression", next);
                                    trace!("<assignee>: <type_id> = >token<");
                                    return Err(AssignmentParseError::UnexpectedEnd);
                                }

                                let (parsed_expr, reached) = parse_expression(tokens, next, 0, true)?;

                                next = reached + 1;

                                if next >= tokens.len() {
                                    error!("unexpected end of tokens at ({}). expected a new line", next);
                                    trace!("<assignee>: <type_id> = <expression> >token<");
                                    return Err(AssignmentParseError::UnexpectedEnd);
                                }

                                match &tokens[next] {
                                    Token::NewLine => {
                                        return Ok(
                                            (
                                                Statement::Assignment { 
                                                    assignee: Box::new(expr_parsed), 
                                                    specified_type: Some(id), 
                                                    expression: Box::new(parsed_expr) 
                                                },
                                                next
                                            )
                                        )
                                    },

                                    wt => {
                                        error!("unexpected token at ({}). expected a new line", next);
                                        trace!("<assignee>: <type_id> = <expression> >token<");
                                        return Err(AssignmentParseError::UnexpectedToken(format!("{:?}", wt)));
                                    }
                                }
                            },

                            wop => {
                                error!("expected '=' but got ({:?}) at ({})", wop, next);
                                trace!("<assignee>: <type_id> >token<");
                                return Err(AssignmentParseError::InvalidOperator);
                            }
                        },

                        _ => {
                            error!("unexpected token at ({}). expected '='", next);
                            trace!("<assignee>: <type_id> >token<");
                            return Err(AssignmentParseError::InvalidOperator);
                        }
                    }
                },

                _ => {
                    error!("invalid type identifier at ({})", next);
                    trace!("<assignee>: >token<");
                    return Err(AssignmentParseError::InvalidTypeIdentifier);
                }
            }
        },

        Token::Operator(op) => match op {
            Operator::AssignmentOrEquality => {
                next += 1;

                if next >= tokens.len() {
                    error!("unexpected end of tokens at ({}). expected an expression", next);
                    trace!("<assignee> = >token<");
                    return Err(AssignmentParseError::UnexpectedEnd);
                }

                let (parsed_expr, reached) = parse_expression(tokens, next, 0, true)?;

                next = reached + 1;

                if next >= tokens.len() {
                    error!("unexpected end of tokens at ({}). expected a new line", next);
                    trace!("<assignee> = .. >token<");
                    return Err(AssignmentParseError::UnexpectedEnd);
                }

                match &tokens[next] {
                    Token::NewLine => {
                        return Ok(
                            (
                                Statement::Assignment { 
                                    assignee: Box::new(expr_parsed),
                                    specified_type: None,
                                    expression: Box::new(parsed_expr) 
                                },
                                next
                            )
                        )
                    },

                    wt => {
                        error!("unexpected token ({:?}) at ({}). expected a new line", wt, next);
                        trace!("<assignee> = .. >token<");
                        return Err(AssignmentParseError::UnexpectedToken(format!("{:?}", wt)));
                    }
                }
            },

            wop => {
                error!("expected '=' but got ({:?}) at ({})", wop, next);
                trace!("<assignee> >token<");
                return Err(AssignmentParseError::InvalidOperator);
            }
        },

        _ => {
            error!("unexpected token at ({}). expected ':' or '='", next);
            trace!("<assignee> >token<");
            return Err(AssignmentParseError::InvalidOperator);
        }
    }
}

/*
 *  if <expression> then
 *      
 *      <instructions> ..
 * 
 *  else if <expression> then 
 *      
 *      <instructions> ..
 * 
 *  else
 *      
 *      <instructions> ..
 * 
 *  end if
*/
fn parse_condition(tokens: &[Token], cursor: usize) -> Result<(ConditionalBlock, usize), ConditionalBlockParseError> {
    let mut begin = cursor;

    let length = tokens.len();

    debug!("parsing a conditional block at ({})", begin);

    if begin >= length {
        error!("unexpected token end. expected 'if' at ({})", begin);
        return Err(ConditionalBlockParseError::UnexpectedEnd);
    }

    match &tokens[begin] {
        Token::Keyword(k) => match k {
            Keyword::If => { },

            i => {
                error!("conditional block did not begin with keyword 'if' at ({})", begin);
                return Err(ConditionalBlockParseError::UnexpectedToken(format!("{:?}", i)));
            }
        },

        t => {
            error!("unexpected token ({:?}) at ({})", t, begin);
            return Err(ConditionalBlockParseError::UnexpectedToken(format!("{:?}", t)));
        }
    };

    begin += 1;

    if begin >= length {
        error!("unexpected token end. expected a conditional expression at ({})", begin);
        return Err(ConditionalBlockParseError::UnexpectedEnd);
    }

    debug!("parsing a conditional expression at ({})", begin);

    let (cond_expr, cond_reached) = parse_expression(tokens, begin, 0, true)?;

    begin = cond_reached + 1;

    if begin >= length {
        error!("unexpected token end. expected 'then' at ({})", begin);
        return Err(ConditionalBlockParseError::UnexpectedEnd);
    }

    match &tokens[begin] {
        Token::Keyword(k) => match k {
            Keyword::Then => {},
            
            i => {
                error!("expected keyword 'then' at ({})", begin);
                return Err(ConditionalBlockParseError::UnexpectedToken(format!("{:?}", i)));
            }
        },

        t => {
            error!("unexpected token ({:?}) at ({}). expected 'then'", t, begin);
            return Err(ConditionalBlockParseError::UnexpectedToken(format!("{:?}", t)));
        }
    };

    // instruction or newline

    begin += 1;

    if begin >= length {
        error!("unexpected token end. expected an instruction or a new line at ({})", begin);
        return Err(ConditionalBlockParseError::UnexpectedEnd);
    }

    match &tokens[begin] {
        Token::NewLine => {
            // parse instructions

            return Err(ConditionalBlockParseError::UnexpectedEnd);
        },

        _ => {
            // parse single instruction
        
            let (parsed_statement, expr_reached) = parse_statement(tokens, begin)
                .map_err(|e| ConditionalBlockParseError::StatementParseError(format!("{e:#?}")))?;

            begin = expr_reached + 1;

            if begin >= length {
                error!("unexpected token end. expected a new line at ({})", begin);
                trace!("if .. then >token<");
                return Err(ConditionalBlockParseError::UnexpectedEnd);
            }

            match &tokens[begin] {
                Token::NewLine => {
                    return Ok(
                        (
                            ConditionalBlock {
                                condition: Box::new(cond_expr),
                                block: Box::new([ parsed_statement ]),
                                else_block: None
                            },

                            begin  
                        )
                    )
                },
                
                Token::Keyword(k) => match k {
                    Keyword::Else => {
                        begin += 1;

                        if begin >= length {
                            error!("unexpected token end. expected an expression at ({})", begin);
                            return Err(ConditionalBlockParseError::UnexpectedEnd);
                        }

                        match &tokens[begin] {
                            Token::Keyword(k) => match k {
                                Keyword::If => {
                                    let (cond_parsed, reached) = parse_condition(tokens, begin)?;

                                    return Ok(
                                        (
                                            ConditionalBlock {
                                                condition: Box::new(cond_expr),
                                                block: Box::new([ parsed_statement ]),
                                                else_block: Some(ElseConditionalBlock::ElseIf(Box::new(cond_parsed)))
                                            },
                                            reached
                                        )
                                    );
                                },

                                wt => {
                                    error!("unexpected token at ({})", begin);
                                    trace!("if .. then .. else >token<");
                                    return Err(ConditionalBlockParseError::UnexpectedToken(format!("{:?}", wt)));
                                }
                            },

                            Token::NewLine => {
                                return Err(ConditionalBlockParseError::UnexpectedEnd);
                            }

                            _ => {

                                let (else_statement_parsed, expr_reached) = parse_statement(tokens, begin)
                                    .map_err(|e| ConditionalBlockParseError::StatementParseError(format!("{e:#?}")))?;

                                begin = expr_reached + 1;

                                if begin >= length {
                                    error!("unexpected end of tokens at ({}). expected a new line", begin);
                                    trace!("if .. then .. else >token<");
                                    return Err(ConditionalBlockParseError::UnexpectedEnd);
                                }

                                match &tokens[begin] {
                                    Token::NewLine => {
                                        return Ok(
                                            (
                                                ConditionalBlock {
                                                    condition: Box::new(cond_expr),
                                                    block: Box::new([ parsed_statement ]),
                                                    else_block: Some(ElseConditionalBlock::Else(Box::new([ else_statement_parsed ])))
                                                },

                                                begin
                                            )
                                        );
                                    },

                                    wt => {
                                        error!("unexpected token at ({}). expected a new line", begin);
                                        trace!("if .. then .. else .. >token<");
                                        return Err(ConditionalBlockParseError::UnexpectedToken(format!("{:?}", wt)));
                                    }
                                }
                            }
                        }
                    },

                    Keyword::End => {
                        begin += 1;

                        if begin >= length {
                            error!("unexpected token end at ({})", begin);
                            return Err(ConditionalBlockParseError::UnexpectedEnd);
                        }

                        match &tokens[begin] {
                            Token::Keyword(kk) => match kk {
                                Keyword::If => {
                                    return Ok(
                                        (
                                            ConditionalBlock {
                                                condition: Box::new(cond_expr),
                                                block: Box::new([ parsed_statement ]),
                                                else_block: None
                                            },

                                            begin
                                        )
                                    )
                                },

                                wk => {
                                    error!("unexpected keyword after 'end' at ({})", begin);
                                    trace!("if .. then .. end >token<");
                                    return Err(ConditionalBlockParseError::UnexpectedToken(format!("{:?}", wk)));
                                }
                            },

                            t => {
                                error!("unexpected token after 'end' at ({})", begin);
                                return Err(ConditionalBlockParseError::UnexpectedToken(format!("{:?}", t))); 
                            }
                        }
                    },

                    wk => {
                        error!("unexpected keyword at ({})", begin);
                        trace!("if .. then .. >token<");
                        return Err(ConditionalBlockParseError::UnexpectedToken(format!("{:?}", wk)));
                    }
                },

                t => {
                    error!("unexpected token at ({})", begin);
                    trace!("if .. then .. >token<");
                    return Err(ConditionalBlockParseError::UnexpectedToken(format!("{:?}", t)));
                }
            }
        }
    }
}

pub fn parse_tokens<T : AsRef<[Token]>>(tokens: T) -> Result<Expression, ExpressionParseError> {
    match parse_expression(tokens.as_ref(), 0, 0, true) {
        Ok((node, _)) => Ok(node),
        Err(e) => Err(e)
    }
}
