use std::borrow::Borrow;
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

    Range {
        begin: Box<Expression>,
        end: Box<Expression>
    },

    InverseRange {
        begin: Box<Expression>,
        end: Box<Expression>
    },

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
    pub patterns: Box<[Expression]>,
    pub block: Box<[Statement]>
}

#[derive(Debug)]
pub enum ElseConditionalBlock {
    ElseIf(Box<ConditionalBlock>),
    Else(Box<[Statement]>),
}

#[derive(Debug)]
pub struct ConditionalBlock {
    pub condition: Expression,
    pub if_block: Box<[Statement]>,
    pub else_block: Option<ElseConditionalBlock>
}

#[derive(Debug)]
pub enum PutPosition {
    Before,
    After,
    Into
}

#[derive(Debug)]
pub enum TheStatement {
    LastCharOf(Expression),
    NumberOfLinesIn(Expression),
    NumberOf(Expression),
    
    The(Expression)
}

#[derive(Debug)]
pub enum ExitArgument {
    Repeat,
    Function
}

#[derive(Debug)]
pub struct SwitchStatement {
    pub condition: Expression,
    pub cases: Box<[SwitchCase]>,
    pub otherwise: Option<Box<[Statement]>>
}

#[derive(Debug)]
pub enum RepeatCondition {
    While(Expression),

    WithNumberRange {
        iterator: Rc<str>,
        begin: Expression,
        end: Expression,
        reversed: bool
    },

    WithListRange{
        iterator: Rc<str>,
        range: Expression
    }
}

#[derive(Debug)]
pub struct RepeatStatement {
    pub condition: RepeatCondition,
    pub block: Box<[Statement]>
}

#[derive(Debug)]
pub struct TypeCast {
    pub identifier:         Rc<str>,
    pub type_identifier:    Rc<str>
}

#[derive(Debug)]
pub struct Variable {
    pub identifier:         Rc<str>,
    pub type_identifier:    Option<Rc<str>>
}

#[derive(Debug)]
pub enum Statement {
    Assignment {
        assignee: Expression,
        specified_type: Option<Rc<str>>,
        expression: Expression
    },

    Condition(ConditionalBlock),

    Switch(SwitchStatement),

    Expression(Expression),

    Put {
        expr: Expression,
        applied_to: Expression,
        position: PutPosition
    },

    The(TheStatement),

    Exit(ExitArgument),
    Global(Box<[ Variable ]>),
    Property(Box<[ Variable ]>),
    TypeSpec(TypeCast),
    Repeat(RepeatStatement),

    Return(Expression)
}


#[derive(Debug)]
pub struct Function {
    pub name:       Rc<str>,
    pub parameters: Box<[Variable]>,
    pub block:      Box<[Statement]>
}

#[derive(Debug)]
pub struct Script {
    pub globals:    Box<[ Variable ]>,
    pub properties: Box<[ Variable ]>,
    pub functions:  Box<[Function]>
}

impl TryFrom<&tokens::Operator> for BinaryOperator {
    type Error = ();

    fn try_from(value: &tokens::Operator) -> Result<Self, Self::Error> {
        use BinaryOperator::*;
        use tokens::Operator;

        match value {
            Operator::Concatenation => Ok(Concatenation),
            Operator::SpaceConcatenation => Ok(SpaceConcatenation),

            Operator::Or => Ok(Or),
            Operator::And => Ok(And),

            Operator::Addition => Ok(Addition),
            Operator::Subtraction => Ok(Subtraction),
            Operator::Multiplication => Ok(Multiplication),
            Operator::Division => Ok(Division),
            Operator::Mod => Ok(Mod),

            Operator::Inequality => Ok(NotEqual),

            Operator::Contains => Ok(Contains),

            Operator::Greater => Ok(Greater),
            Operator::Smaller => Ok(Smaller),
            Operator::GreaterOrEqual => Ok(GreaterOrEqual),
            Operator::SmallerOrEqual => Ok(SmallerOrEqual),
            Operator::AssignmentOrEquality => Ok(Equal),

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
        use BinaryOperator::*;

        write!(f, "{}", match self {
            And                 => "and",
            Or                  => "or",
            Addition            => "+",
            Subtraction         => "-",
            Multiplication      => "*",
            Division            => "/",
            Greater             => ">",
            Smaller             => "<",
            GreaterOrEqual      => ">=",
            SmallerOrEqual      => "<=",
            Contains            => "contains",
            Starts              => "starts",
            Concatenation       => "&",
            SpaceConcatenation  => "&&",
            Mod                 => "mod",
            Equal               => "=",
            NotEqual            => "<>",
        })
    }
}

impl Display for UnaryOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use UnaryOperator::*;
        
        write!(f, "{}", match self {
            Negate   => "not ",
            Negative => "-",
            Positive => "+",
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
    use tokens::Operator::*;
    
    match op {
        Dot                     => 6,
        Contains                => 1,
        Starts                  => 1,
        Concatenation           => 2,
        SpaceConcatenation      => 2,
        Or                      => 4,
        And                     => 4,
        Addition                => 3,
        Subtraction             => 3,
        Multiplication          => 4,
        Division                => 4,
        Mod                     => 4,
        Inequality              => 1,
        Greater                 => 1,
        Smaller                 => 1,
        GreaterOrEqual          => 1,
        SmallerOrEqual          => 1,
        AssignmentOrEquality    => 0,
        Not                     => 5
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
pub enum VariableDeclarationsParseError {
    #[error("unexpected error")]
    UnexpectedError,

    #[error("unexpected end of tokens")]
    UnexpectedEnd,

    #[error("failed to parse variable declaration")]
    Variable(#[from] VariableParseError)
}

#[derive(Debug, thiserror::Error)]
pub enum CaseBlockParseError {
    #[error("unexpected end")]
    UnexpectedEnd,

    #[error("unexpected token")]
    UnexpectedToken,

    #[error("failed to parse statement")]
    Statement(#[from ]StatementParseError),

    #[error("switch case block was empty")]
    EmptyBlock
}

#[derive(Debug, thiserror::Error)]
pub enum SwitchParseError {
    #[error("unexpected end")]
    UnexpectedEnd,

    #[error("unexpected token")]
    UnexpectedToken,

    #[error("failed to parse switch expression")]
    SwitchExpression,

    #[error("failed to parse a switch case statement block")]
    CaseBlock(#[from] CaseBlockParseError),

    #[error("otherwise case is already defined")]
    DoubleOtherwise,

    #[error("failed to parse case pattern")]
    CasePattern,

    #[error("invalid switch case pattern. must be a constant literal")]
    InvalidCasePattern,
}

#[derive(Debug, thiserror::Error)]
pub enum PutStatementParseError {
    #[error("failed to parse put's expression")]
    PutExpr(#[from] ExpressionParseError),

    #[error("unexpected token")]
    UnexpectedToken,

    #[error("unexpected end")]
    UnexpectedEnd,
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
    Assignment(#[from] AssignmentParseError),

    #[error("failed to parse put statement")]
    Put(#[from] PutStatementParseError),

    #[error("failed to parse global declaration statement")]
    Global(#[from] VariableDeclarationsParseError),
    
    #[error("failed to parse switch statement")]
    Switch,

    #[error("failed to parse repeat statement")]
    Repeat,

    #[error("failed to parse type cast statement")]
    TypeCast(#[from] TypeCastStatementParseError),

    #[error("failed to parse expression")]
    Expression(#[from] ExpressionParseError)
}

#[derive(Debug, thiserror::Error)]
pub enum StatementBlockParseError {
    #[error("unexpected end")]
    UnexpectedEnd,

    #[error("expected a new line")]
    ExpectedNewLine,

    #[error("failed to parse statement")]
    Statement(#[from] StatementParseError)
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
pub enum RepeatParseError {
    #[error("unexpected end of tokens")]
    UnexpectedEnd,

    #[error("unexpected token")]
    UnexpectedToken,

    #[error("failed to parse conditional expression")]
    ConditionalExpression(#[from] ExpressionParseError),

    #[error("failed to parse conditional assignment")]
    ConditionalAssignment(#[from] AssignmentParseError),

    #[error("failed to parse repeat header")]
    Header(#[from] RepeatHeaderParseError),

    #[error("invalid conditional assignment")]
    InvalidConditionalAssignment,

    #[error("failed to parse repeat statement block")]
    StatementBlock(#[from] RepeatStatementBlockParseError)
}

#[derive(Debug, thiserror::Error)]
pub enum RepeatHeaderParseError {
    #[error("unexpected end of tokens")]
    UnexpectedEnd,

    #[error("unexpected token")]
    UnexpectedToken,

    #[error("failed to parse repeat header")]
    HeaderExpression(#[from] ExpressionParseError),
}

#[derive(Debug, thiserror::Error)]
pub enum RepeatStatementBlockParseError {
    #[error("unexpected end of tokens")]
    UnexpectedEnd,

    #[error("unexpected token")]
    UnexpectedToken,

    #[error("failed to parse statement")]
    Statement(#[from] StatementParseError)
}

#[derive(Debug, thiserror::Error)]
pub enum TypeCastStatementParseError {
    #[error("unexpected end of tokens")]
    UnexpectedEnd,

    #[error("unexpected token")]
    UnexpectedToken,

    #[error("invalid casted identifier")]
    InvalidIdentifier,

    #[error("invalid type identifier")]
    InvalidType,

    #[error("failed to parse type cast identifier expression")]
    IdentifierParse(#[from] ExpressionParseError)
}

#[derive(Debug, thiserror::Error)]
pub enum VariableParseError {
    #[error("unexpected end of tokens")]
    UnexpectedEnd,

    #[error("unexpected token")]
    UnexpectedToken,

    #[error("invalid casted identifier")]
    InvalidIdentifier,

    #[error("invalid type identifier")]
    InvalidType,

    #[error("failed to parse type cast identifier expression")]
    IdentifierParse(#[from] ExpressionParseError)
}

#[derive(Debug, thiserror::Error)]
pub enum FunctionParseError {
    #[error("unexpected end of tokens")]
    UnexpectedEnd,

    #[error("unexpected token")]
    UnexpectedToken,

    #[error("invalid function name. expected an identifier")]
    InvalidName,

    #[error("invalid function parameter. expected an identifier")]
    Prameter(#[from] VariableParseError),

    #[error("failed to parse function block statement")]
    BlockStatement(#[from] StatementParseError)
}

#[derive(Debug, thiserror::Error)]
pub enum ScriptParseError {
    #[error("script is empty")]
    Empty,

    #[error("failed to parse global variables")]
    Variable(#[from] VariableDeclarationsParseError),

    #[error("failed to parse function")]
    Function(#[from] FunctionParseError)
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
            error!("unexpected token ',' at ({})", begin);
            return Err(ExpressionParseError::UnexpectedToken { character: format!("{:?}", Token::Comma) });
        },
        Token::Colon => {
            error!("unexpected token ':' at ({})", begin);
            return Err(ExpressionParseError::UnexpectedToken { character: format!("{:?}", Token::Colon) });
        },
        Token::CloseBracket => {
            error!("unexpected token ']' at ({})", begin);
            return Err(ExpressionParseError::UnexpectedToken { character: format!("{:?}", Token::CloseBracket) });
        },
        Token::CloseParenthesis => {
            error!("unexpected token ')' at ({})", begin);
            return Err(ExpressionParseError::UnexpectedToken { character: format!("{:?}", Token::CloseParenthesis) });
        },

        Token::NewLine => {
            error!("unexpected new line at ({})", begin);
            return Err(ExpressionParseError::UnexpectedToken { character: format!("\"\"") });
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

        Token::Keyword(k) => match k {
            Keyword::Item | 
            Keyword::Char |
            Keyword::Word |
            Keyword::Line => {
                begin += 1;

                if begin >= length {
                    error!("unexpected end of tokens at ({}). expected an expression", begin);
                    return Err(ExpressionParseError::UnexpectedEnd);
                }

                let (range_expr, reached) = parse_expression(tokens, begin, min_precedence, true)?;

                begin = reached + 1;

                if begin >= length {
                    error!("unexpected end of tokens at ({}). expected 'of' or 'to'", begin);
                    return Err(ExpressionParseError::UnexpectedEnd);
                }

                match &tokens[begin] {
                    Token::Keyword(sk) => match sk {
                        Keyword::Of => {
                            begin += 1;

                            if begin >= length {
                                error!("unexpected end of tokens at ({}). expected an expression", begin);
                                return Err(ExpressionParseError::UnexpectedEnd);
                            }

                            let (chunk, reached) = parse_expression(tokens, begin, min_precedence, true)?;

                            match range_expr {
                                Expression::Range { begin, end } => {
                                    parse_res = Ok(
                                        (
                                            Expression::PostOperation { 
                                                left: Box::new(chunk), 
                                                operator: PostOperator::Slice { begin, end } 
                                            },
        
                                            reached
                                        )
                                    )
                                }, 
                                
                                Expression::InverseRange { begin, end } => {
                                    parse_res = Ok(
                                        (
                                            Expression::PostOperation { 
                                                left: Box::new(chunk), 
                                                operator: PostOperator::Slice { begin, end } 
                                            },
        
                                            reached
                                        )
                                    )
                                },

                                index => {
                                    parse_res = Ok(
                                        (
                                            Expression::PostOperation { 
                                                left: Box::new(chunk), 
                                                operator: PostOperator::Index(Box::new(index)) 
                                            },
        
                                            reached
                                        )
                                    )
                                }
                            }
                        },

                        wk => {
                            error!("unexpected token at ({}). expected 'of' or 'to'", begin);
                            return Err(ExpressionParseError::UnexpectedToken { character: format!("{:?}", wk) });
                        }
                    },

                    wt => {
                        error!("unexpected token at ({}). expected 'of' or 'to'", begin);
                        return Err(ExpressionParseError::UnexpectedToken { character: format!("{:?}", wt) });
                    }
                }
            },

            
            
            _ => {
                return Err(ExpressionParseError::UnexpectedToken { character: format!("{:?}", k) });
            }
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
                            if commad && !args.is_empty() {
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

                    tokens::Operator::AssignmentOrEquality => {
                        if !equals {
                            return Ok(
                                (
                                    subtree,
                                    begin
                                )
                            )
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

            Token::Keyword(k) => match k {
                Keyword::To => {
                    let next = begin + 2;

                    if next >= length {
                        error!("unexpected end of tokens at ({}). expected an expression", next);
                        return Err(ExpressionParseError::UnexpectedEnd);
                    }

                    let (second_expr, reached) = parse_expression(tokens, next, min_precedence, true)?;

                    subtree = Expression::Range { 
                        begin: Box::new(subtree), 
                        end: Box::new(second_expr)
                    };

                    begin = reached;
                },

                Keyword::Down => {
                    let next = begin + 2;

                    if next >= length {
                        error!("unexpected end of tokens at ({}). expected a keyword", next);
                        return Err(ExpressionParseError::UnexpectedEnd);
                    }

                    match &tokens[next] {
                        Token::Keyword(k) => match k {
                            Keyword::To => {
                                let next = next + 1;

                                if next >= length {
                                    error!("unexpected end of tokens at ({}). expected an expression", next);
                                    return Err(ExpressionParseError::UnexpectedEnd);
                                }

                                let (second_expr, reached) = parse_expression(tokens, next, min_precedence, true)?;

                                subtree = Expression::InverseRange { 
                                    begin: Box::new(subtree), 
                                    end: Box::new(second_expr)
                                };

                                begin = reached;
                            },

                            wk => {
                                error!("unexpected keyword at ({}). expected keyword 'to'", next);
                                return Err(ExpressionParseError::UnexpectedToken { character: format!("{:?}", wk) });
                            }
                        },

                        wt => {
                            error!("unexpected token at ({}). expected keyword 'to'", next);
                            return Err(ExpressionParseError::UnexpectedToken { character: format!("{:?}", wt) });
                        }
                    }
                },

                _ => break 'op_loop
            }

            _ => break 'op_loop
        }
    }


    Ok((subtree, begin))
}

fn parse_statement(tokens: &[Token], cursor: usize) -> Result<(Statement, usize), StatementParseError> {
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
                );
            },

            Keyword::Put => {
                let (parsed_put, reached) = parse_put_statement(tokens, cursor)?;

                return Ok(
                    (
                        parsed_put,
                        reached
                    )
                );
            },

            Keyword::Global => {
                let (globals, reached) = parse_variable_declarations(tokens, cursor + 1)?;

                return Ok(
                    (
                        Statement::Global(globals.into()),
                        reached
                    )
                );
            },

            Keyword::Property => {
                let (globals, reached) = parse_variable_declarations(tokens, cursor + 1)?;

                return Ok(
                    (
                        Statement::Property(globals.into()),
                        reached
                    )
                );
            }

            Keyword::Exit => {
                let mut next = cursor + 1;

                if next >= tokens.len() {
                    error!("unexpected end of tokens at ({}). expected 'repeat' or a new line", next);
                    return Err(StatementParseError::UnexpectedEnd);
                }

                match &tokens[next] {
                    Token::Keyword(k) => match k {
                        Keyword::Repeat => {
                            next += 1;

                            if next >= tokens.len() {
                                error!("unexpected end of tokens at ({}). expected a new line", next);
                                return Err(StatementParseError::UnexpectedEnd);
                            }

                            match &tokens[next] {
                                Token::NewLine => {
                                    return Ok(
                                        (
                                            Statement::Exit(ExitArgument::Repeat),
                                            next
                                        )
                                    )
                                },

                                wt => {
                                    error!("unexpected token ({:?}) at ({}). expected a new line", wt, next);
                                    return Err(StatementParseError::UnexpectedToken(format!("{:?}", wt)));
                                }
                            }
                        },

                        wk => {
                            error!("unexpected keyword ({:?}) at ({}). expected 'repeat'", wk, next);
                            return Err(StatementParseError::UnexpectedToken(format!("{:?}", wk)));
                        }
                    },

                    Token::NewLine => {
                        return Ok(
                            (
                                Statement::Exit(ExitArgument::Function),
                                next
                            )
                        );
                    },

                    wt => {
                        error!("unexpected token ({:?}) at ({})", wt, next);
                        return Err(StatementParseError::UnexpectedToken(format!("{:?}", wt)));
                    }
                }
            }

            Keyword::Return => {
                let mut next = cursor + 1;

                if next >= tokens.len() {
                    error!("unexpected end of tokens at ({}). expected an expression or a new line", next);
                    return Err(StatementParseError::UnexpectedEnd);
                }

                match &tokens[next] {
                    Token::NewLine => {
                        return Ok(
                            (
                                Statement::Return(Expression::Void),
                                next
                            )
                        );
                    },

                    _ => {
                        let (returned_expr, reached) = parse_expression(tokens, next, 0, true)
                            .map_err(|e| StatementParseError::UnexpectedToken(format!("{:?}", e)))?;

                        next = reached + 1;

                        if next >= tokens.len() {
                            error!("unexpected end of tokens at ({}). expected a new line", next);
                            return Err(StatementParseError::UnexpectedEnd);
                        }

                        match &tokens[next] {
                            Token::NewLine => {
                                return Ok(
                                    (
                                        Statement::Return(returned_expr),
                                        next
                                    )
                                );
                            },

                            wt => {
                                error!("unexpected token at ({})", next);
                                return Err(StatementParseError::UnexpectedToken(format!("{:?}", wt)));
                            }
                        }
                    }
                }
            },

            Keyword::Case => {
                let (switch, reached) = parse_switch_statement(tokens, cursor).map_err(|_| StatementParseError::Switch)?;
            
                return Ok(
                    (
                        Statement::Switch(switch),
                        reached
                    )
                );
            },

            Keyword::Repeat => {
                let (repeat, reached) = parse_repeat_statement(tokens, cursor)
                    .map_err(|_| StatementParseError::Repeat)?;

                return Ok(
                    (
                        Statement::Repeat(repeat),
                        reached
                    )
                );
            },

            Keyword::Type => {
                let (cast, reached) = parse_type_cast_statement(tokens, cursor)?;
            
                return Ok(
                    (
                        Statement::TypeSpec(cast),
                        reached
                    )
                );
            },

            wk => {
                error!("unexpected keyword at ({})", cursor);
                return Err(StatementParseError::UnexpectedToken(format!("{:?}", wk)));
            }
        },

        Token::NewLine => {
            error!("unexpected leading new line at ({cursor})");
            return Err(StatementParseError::UnexpectedToken("<new line>".into()));
        }

        _ => {
            // attempt to parse an assignment

            debug!("attempting to parse an assignment at ({})", cursor);

            match parse_assignment(tokens, cursor) {
                Ok((assignment, reached)) => {
                    return Ok(
                        (
                            assignment,
                            reached
                        )
                    );
                },

                Err(_) => {
                    // on failure, attempt to parse an expression

                    debug!("assignment parse failure; attempting to parse an expression at ({})", cursor);

                    match parse_expression(tokens, cursor, 0, true) {
                        Ok((expr, reached)) => {
                            return Ok(
                                (
                                    Statement::Expression(expr),
                                    reached
                                )
                            );
                        },

                        Err(e) => {
                            error!("failed to parse expression at ({})", cursor);
                            return Err(StatementParseError::Expression(e));
                        }
                    }
                }
            }
        }
    }
}

fn parse_type_cast_statement(tokens: &[Token], cursor: usize) -> Result<(TypeCast, usize), TypeCastStatementParseError> {
    use TypeCastStatementParseError::*;
    
    debug!("parsing a type cast at ({})", cursor);

    if cursor >= tokens.len() {
        error!("unexpected end of tokens at ({}). expected 'type'", cursor);
        return Err(UnexpectedEnd);
    }

    if tokens[cursor] != Token::Keyword(Keyword::Type) {
        error!("unexpected token ({:?}) at ({}). expected 'type'", &tokens[cursor], cursor);
        return Err(UnexpectedToken);
    }

    let mut next = cursor + 1;

    if next >= tokens.len() {
        error!("unexpected end of tokens at ({}). expected an identifer", next);
        return Err(UnexpectedEnd);
    }

    let identifier = if let Token::Identifier(iden) = &tokens[next] {
        Ok(Rc::clone(iden))
    } else {
        error!("unexpected token ({:?}) at ({}). expected an identifier", &tokens[next], next);
        Err(InvalidIdentifier)
    }?;

    next += 1;

    if next >= tokens.len() {
        error!("unexpected end of tokens at ({}). expected ':'", next);
        return Err(UnexpectedEnd);
    }

    if tokens[next] != Token::Colon {
        error!("unexpected token ({:?}) at ({}). expected ':'", &tokens[cursor], cursor);
        return Err(UnexpectedToken);
    }

    next += 1;

    if next >= tokens.len() {
        error!("unexpected end of tokens at ({}). expected an identifier", next);
        return Err(UnexpectedEnd);
    }

    let type_identifier = if let Token::Identifier(iden) = &tokens[next] {
        Ok(Rc::clone(iden))
    } else {
        error!("unexpected token ({:?}) at ({}). expected a type identifier", &tokens[next], next);
        Err(InvalidType)
    }?;

    Ok(
        (
            TypeCast {
                identifier,
                type_identifier
            },

            next
        )
    )
}

fn parse_variable_declaration(tokens: &[Token], cursor: usize) -> Result<(Variable, usize), VariableParseError> {
    use VariableParseError::*;
    
    debug!("parsing a function parameter at ({})", cursor);

    if cursor >= tokens.len() {
        error!("unexpected end of tokens at ({}). expected 'type'", cursor);
        return Err(UnexpectedEnd);
    }

    let mut next = cursor;

    if next >= tokens.len() {
        error!("unexpected end of tokens at ({}). expected an identifer", next);
        return Err(UnexpectedEnd);
    }

    let identifier = if let Token::Identifier(iden) = &tokens[next] {
        Ok(Rc::clone(iden))
    } else {
        error!("unexpected token ({:?}) at ({}). expected an identifier", &tokens[next], next);
        Err(InvalidIdentifier)
    }?;

    let peek = next + 1;

    if peek >= tokens.len() {
        error!("unexpected end of tokens at ({}). expected ':'", peek);
        return Err(UnexpectedEnd);
    }

    if tokens[peek] != Token::Colon {
        return Ok(
            (
                Variable {
                    identifier,
                    type_identifier: None
                },

                next
            )
        );
    }

    next += 2;

    if next >= tokens.len() {
        error!("unexpected end of tokens at ({}). expected an identifier", next);
        return Err(UnexpectedEnd);
    }

    let type_identifier = if let Token::Identifier(iden) = &tokens[next] {
        Ok(Rc::clone(iden))
    } else {
        error!("unexpected token ({:?}) at ({}). expected a type identifier", &tokens[next], next);
        Err(InvalidType)
    }?;

    Ok(
        (
            Variable {
                identifier,
                type_identifier: Some(type_identifier)
            },

            next
        )
    )
}

fn parse_conditional_statement_block(tokens: &[Token], cursor: usize) -> Result<(Box<[Statement]>, usize), StatementBlockParseError> {
    debug!("parsing a conditional statement block");
    
    if cursor >= tokens.len() {
        error!("unexpected end of tokens");
        return Err(StatementBlockParseError::UnexpectedEnd);
    }

    let mut next = cursor;
    let mut statements = vec![];

    'statement_loop: loop {
        if next >= tokens.len() {
            error!("unexpected end of tokens at ({}). expected a statement or 'end'", next);
            return Err(StatementBlockParseError::UnexpectedEnd);
        }

        if tokens[next] == Token::Keyword(Keyword::End) || tokens[next] == Token::Keyword(Keyword::Else) {
            next -= 1;
            break 'statement_loop;
        }

        debug!("parsing statement #{} at ({})", statements.len() + 1, next);

        let (statement, reached) = parse_statement(tokens, next)?;

        statements.push(statement);
        
        next = reached + 1;

        if tokens[next] != Token::NewLine {
            error!("unexpected ({:?}) at ({}). expected a new line", &tokens[next], next);
            return Err(StatementBlockParseError::ExpectedNewLine);
        }

        let peek_next = next + 1;

        if peek_next >= tokens.len() {
            error!("unexpected end of tokens at ({}). expected a statement or 'end'", peek_next);
            return Err(StatementBlockParseError::UnexpectedEnd);
        }

        if tokens[peek_next] == Token::Keyword(Keyword::End) {
            break 'statement_loop;
        }

        next += 1;
    }

    Ok(
        (
            statements.into(),
            next
        )
    )
}

fn parse_put_statement(tokens: &[Token], cursor: usize) -> Result<(Statement, usize), PutStatementParseError> {
    debug!("parsing put statement at ({})", cursor);
    
    let mut next = cursor + 1;

    if next >= tokens.len() {
        error!("unexpected end at ({}). expected an expression", next);
        return Err(PutStatementParseError::UnexpectedEnd);
    }

    let (to_be_put, reached) = parse_expression(tokens, next, 0, true)?;

    next = reached + 1;

    if next >= tokens.len() {
        error!("unexpected end at ({}). expected 'into', 'before', or 'after'", next);
        return Err(PutStatementParseError::UnexpectedEnd);
    }

    let pos: PutPosition = match &tokens[next] {
        Token::Keyword(k) => match k {
            Keyword::Before => Ok(PutPosition::Before),
            Keyword::After => Ok(PutPosition::After),
            Keyword::Into => Ok(PutPosition::Into),

            _ => Err(PutStatementParseError::UnexpectedToken)
        },

        _ => Err(PutStatementParseError::UnexpectedToken)
    }?;

    next += 1;

    if next >= tokens.len() {
        error!("unexpected end at ({}). expected an expression", next);
        return Err(PutStatementParseError::UnexpectedEnd);
    }

    let (put_into, reached) = parse_expression(tokens, next, 0, false)?;

    next = reached + 1;

    if next >= tokens.len() {
        error!("unexpected end at ({}). expected a new line", next);
        return Err(PutStatementParseError::UnexpectedEnd);
    }

    match &tokens[next] {
        Token::NewLine => {
            return Ok(
                (
                    Statement::Put { 
                        expr: to_be_put, 
                        applied_to: put_into, 
                        position: pos 
                    },

                    next
                )
            )
        },

        wt => {
            error!("unexpected token ({:?}) at ({}). expected a new line", wt, next);
            return Err(PutStatementParseError::UnexpectedToken);
        }
    }
}

fn parse_variable_declarations(tokens: &[Token], cursor: usize) -> Result<(Vec<Variable>, usize), VariableDeclarationsParseError> {
    if cursor >= tokens.len() {
        error!("unexpected end of tokens at ({})", cursor);
        return Err(VariableDeclarationsParseError::UnexpectedEnd);
    }
    
    let mut identifiers = vec![];

    let mut commad = true;

    let mut next = cursor + 1;

    'g_loop: while next < tokens.len() {
        match &tokens[next] {
            Token::Identifier(_) => {
                if !commad {
                    error!("expected a comma at ({})", next);
                    return Err(VariableDeclarationsParseError::UnexpectedError);
                }

                commad = false;

                let (parsed_var, reached) = parse_variable_declaration(tokens, next)?;

                identifiers.push(parsed_var);
                next = reached;
            },

            Token::Comma => {
                if commad {
                    error!("unexpected comma at ({})", next);
                    return Err(VariableDeclarationsParseError::UnexpectedError);
                }

                commad = true;
            },

            Token::NewLine => {
                break 'g_loop;
            },

            _ => {
                error!("unexpected token at ({})", next);
                return Err(VariableDeclarationsParseError::UnexpectedError);
            }
        }

        next += 1;
    }

    Ok((
        identifiers,
        next
    ))
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

                                return Ok(
                                    (
                                        Statement::Assignment { 
                                            assignee: expr_parsed, 
                                            specified_type: Some(id), 
                                            expression: parsed_expr 
                                        },
                                        reached
                                    )
                                );
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

                return Ok(
                    (
                        Statement::Assignment { 
                            assignee: expr_parsed,
                            specified_type: None,
                            expression: parsed_expr 
                        },
                        reached
                    )
                );
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

fn parse_switch_case_statements_block(tokens: &[Token], cursor: usize) -> Result<(Box<[Statement]>, usize), CaseBlockParseError> {
    debug!("parsing a switch case statement block at ({})", cursor);

    let mut next = cursor;
    let mut statements = vec![];

    loop {
        let (statement, reached) = parse_statement(tokens, next)?;

        match &statement {
            Statement::Expression(e) => {
                match e {
                    Expression::Integer(_) |
                    Expression::Float(_) |
                    Expression::String(_) |
                    Expression::Symbol(_) => {
                        let peek_next = reached + 1;

                        if peek_next >= tokens.len() {
                            error!("unexpected end of tokens at ({})", peek_next);
                            return Err(CaseBlockParseError::UnexpectedEnd);
                        }
            
                        if tokens[peek_next] == Token::Colon || tokens[peek_next] == Token::Comma {
                            if statements.is_empty() {
                                error!("empty switch case statement");
                                return Err(CaseBlockParseError::EmptyBlock);
                            }

                            return Ok(
                                (
                                    statements.into(),
                                    next - 1
                                )
                            );
                        }
                    },

                    _ => { }
                }
            },

            _ => { }
        }
    
        statements.push(statement);

        next = reached;

        if next + 1 >= tokens.len() {
            error!("unexpected end of tokens at ({}). expected a new line", next + 1);
            return Err(CaseBlockParseError::UnexpectedEnd);
        }

        next += 1;

        while tokens[next] == Token::NewLine { 
            next += 1;

            if next >= tokens.len() {
                error!("unexpected end of tokens at ({}). expected a new line", next);
                return Err(CaseBlockParseError::UnexpectedEnd);
            }
        }

        if tokens[next] == Token::Keyword(Keyword::Otherwise) {
            return Ok(
                (
                    statements.into(),
                    next - 1
                )
            );
        }

        if tokens[next] == Token::Keyword(Keyword::End) {
            let peek_next = next + 1;

            if peek_next >= tokens.len() {
                error!("unexpected end of tokens at ({}). expected 'case'", peek_next);
                return Err(CaseBlockParseError::UnexpectedEnd);
            }

            if tokens[peek_next] == Token::Keyword(Keyword::Case) {
                return Ok(
                    (
                        statements.into(),
                        next - 1
                    )
                );
            }
        }
    }
}

/// consumes 'end repeat'
fn parse_repeat_statement_block(tokens: &[Token], cursor: usize) -> Result<(Box<[Statement]>, usize), RepeatStatementBlockParseError> {
    use RepeatStatementBlockParseError::*;

    debug!("parsing repeat statement block at ({})", cursor);

    let mut statements = vec![];

    let mut next = cursor;

    loop {
        if next >= tokens.len() {
            error!("unexpected end of tokens at ({}). expected a new line, statement, or 'end'", next);
            return Err(UnexpectedEnd);
        }

        while tokens[next] == Token::NewLine {
            next += 1;
    
            if next >= tokens.len() {
                error!("unexpected end of tokens at ({}). expected a new line, statement, or 'end'", next);
                return Err(UnexpectedEnd);
            }
        }
    
        if tokens[next] == Token::Keyword(Keyword::End) {
            let peek = next + 1;

            if peek >= tokens.len() {
                error!("unexpected end of tokens at ({}). expected 'repeat'", peek);
                return Err(UnexpectedEnd);
            }

            if tokens[peek] != Token::Keyword(Keyword::Repeat) {
                error!("unexpected token ({:?}) at ({}). expected 'repeat'", &tokens[peek], peek);
                return Err(UnexpectedToken);
            }

            return Ok(
                (
                    statements.into(),
                    peek
                )
            );
        }

        debug!("parsing repeat statement #({})", statements.len() + 1);

        let (statement, reached) = parse_statement(tokens, next)?;

        statements.push(statement);

        next = reached + 1;

        debug!("successfully parsed statement #({}). reached ({})", statements.len(), next);
    }
}

fn parse_switch_statement(tokens: &[Token], cursor: usize) -> Result<(SwitchStatement, usize), SwitchParseError> {
    debug!("parsing a switch statement at ({})", cursor);

    if cursor >= tokens.len() {
        error!("unexpected end of tokens at ({})", cursor);
        return Err(SwitchParseError::UnexpectedEnd);
    }

    match &tokens[cursor] {
        Token::Keyword(k) => match k {
            Keyword::Case => { },
            wk => {
                error!("unexpected keyword({:?}) at ({})", wk, cursor);
                return Err(SwitchParseError::UnexpectedToken);
            }
        },

        wt => {
            error!("unexpected token ({:?}) at ({})", wt, cursor);
            return Err(SwitchParseError::UnexpectedToken);
        }
    }

    let mut next = cursor + 1;

    if next >= tokens.len() {
        error!("unexpected end of tokens at ({}). expected an expression", next);
        trace!("case >token<");
        return Err(SwitchParseError::UnexpectedEnd);
    }

    let (switch_expr, reached) = parse_expression(tokens, next, 0, true)
        .map_err(|_| SwitchParseError::SwitchExpression)?;

    next = reached + 1;

    if next >= tokens.len() {
        error!("unexpected end of tokens at ({}). expected 'of'", next);
        trace!("case >token<");
        return Err(SwitchParseError::UnexpectedEnd);
    }

    if tokens[next] != Token::Keyword(Keyword::Of) {
        error!("unexpected token ({:?}) at ({}). expected 'of'", &tokens[next], cursor);
        trace!("case <expr> >token<");
        return Err(SwitchParseError::UnexpectedToken);
    }

    next += 1;

    if next >= tokens.len() {
        error!("unexpected end of tokens at ({}). expected a new line", next);
        trace!("case <expr> of >token<");
        return Err(SwitchParseError::UnexpectedEnd);
    }

    while tokens[next] == Token::NewLine { next += 1; }

    if next >= tokens.len() {
        error!("unexpected end of tokens at ({})", next);
        trace!("case <expr> of .. >token<");
        return Err(SwitchParseError::UnexpectedEnd);
    }

    let mut cases = vec![];
    let mut otherwise = None;

    loop {
        match &tokens[next] {
            Token::Keyword(k) => match k {
                Keyword::End => {
                    next += 1;

                    if next >= tokens.len() {
                        error!("unexpected end of tokens at ({}). expected 'case'", next);
                        trace!("case <expr> of .. end >token<");
                        return Err(SwitchParseError::UnexpectedEnd);
                    }

                    match &tokens[next] {
                        Token::Keyword(k) => match k {
                            Keyword::Case => {
                                return Ok(
                                    (
                                        SwitchStatement {
                                            condition: switch_expr,
                                            cases: cases.into(),
                                            otherwise
                                        },

                                        next
                                    )
                                );
                            },

                            wk => {
                                error!("unexpected keyword ({:?}) at ({}). expected 'case'", wk, next);
                                trace!("case <expr> of .. end >token<");
                                return Err(SwitchParseError::UnexpectedToken);
                            }
                        },

                        wt => {
                            error!("unexpected token ({:?}) at ({}). expected 'case'", wt, next);
                            trace!("case <expr> of .. end >token<");
                        }
                    }
                },

                Keyword::Otherwise => {
                    if otherwise.is_some() {
                        error!("'otherwise' case has already been defined");
                        return Err(SwitchParseError::DoubleOtherwise);
                    }

                    next += 1;

                    if next >= tokens.len() {
                        error!("unexpected end of tokens at ({}). expected ':'", next);
                        trace!("case <expr> of\n\t..\n\totherwise >token<");
                        return Err(SwitchParseError::UnexpectedEnd);
                    }

                    if tokens[next] != Token::Colon {
                        error!("unexpected token at ({}). expected ':'", next);
                        trace!("case <expr> of\n\t..\n\totherwise >token<");
                        return Err(SwitchParseError::UnexpectedToken);
                    }

                    next += 1;

                    if next >= tokens.len() {
                        error!("unexpected token at ({}). expected a statement or a new line", next);
                        trace!("case <expr> of\n\t..\n\totherwise: >token<");
                        return Err(SwitchParseError::UnexpectedToken);
                    }

                    if tokens[next] == Token::NewLine {
                        next += 1;

                        if next >= tokens.len() {
                            error!("unexpected token at ({}). expected a statement", next);
                            trace!("case <expr> of\n\t..\n\totherwise: >token<");
                            return Err(SwitchParseError::UnexpectedToken);
                        }
                    }

                    let (block, reached) = parse_switch_case_statements_block(tokens, next)?;

                    otherwise = Some(block);
                    next = reached;
                }
            
                wk => {
                    error!("unexpected keyword ({:?}) at ({}). expected an expression", wk, next);
                    return Err(SwitchParseError::UnexpectedToken);
                }
            },

            _ => {
                let mut patterns = vec![];

                'case_loop: loop {
                    let (pattern, p_reached) = parse_expression(tokens, next, 0, false)
                        .map_err(|_| SwitchParseError::CasePattern)?;

                    
                    match &pattern {
                        Expression::Integer(_) |
                        Expression::Float(_) |
                        Expression::String(_) |
                        Expression::Symbol(_) => {
    
                        },
    
                        _ => {
                            error!("invalid switch case pattern at ({})", next);
                            return Err(SwitchParseError::InvalidCasePattern);
                        }
                    }

                    patterns.push(pattern);
                
                    next = p_reached + 1;
    
                    if next >= tokens.len() {
                        error!("unexpected end of tokens at ({}). expected ':' or ','", next);
                        return Err(SwitchParseError::UnexpectedEnd);
                    }
                    
                    if tokens[next] != Token::Colon && tokens[next] != Token::Comma {
                        error!("unexpected token at ({}). expected ':' or ','", next);
                        return Err(SwitchParseError::UnexpectedToken);
                    }
    
                    if tokens[next] == Token::Comma { next += 1; continue 'case_loop; }

                    if tokens[next] != Token::Colon { 
                        error!("unexpected token ({:?}) at ({}). expected ':'", &tokens[next], next);
                        return Err(SwitchParseError::UnexpectedToken); 
                    }

                    break 'case_loop;
                }

                next += 1;

                while tokens[next] == Token::NewLine { next += 1; }

                let (block, reached) = parse_switch_case_statements_block(tokens, next)?;

                cases.push(SwitchCase{ patterns: patterns.into(), block });

                next = reached;
            }
        }

        next += 1;

        if next >= tokens.len() {
            error!("unexpected end of tokens at ({}). expected an expression or 'end'", next);
            return Err(SwitchParseError::UnexpectedEnd);
        }
    }
}

fn parse_condition(tokens: &[Token], cursor: usize) -> Result<(ConditionalBlock, usize), ConditionalBlockParseError> {
    let mut begin = cursor;

    let length = tokens.len();

    debug!("parsing a conditional block at ({})", begin);

    if begin >= length {
        error!("unexpected token end. expected 'if' at ({})", begin);
        return Err(ConditionalBlockParseError::UnexpectedEnd);
    }

    if tokens[begin] != Token::Keyword(Keyword::If) {
        error!("unexpected token ({:?}) at ({})", &tokens[begin], begin);
        return Err(ConditionalBlockParseError::UnexpectedToken(format!("{:?}", &tokens[begin])));
    }

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

    if tokens[begin] != Token::Keyword(Keyword::Then) {
        error!("unexpected token ({:?}) at ({}). expected 'then'", &tokens[begin], begin);
        return Err(ConditionalBlockParseError::UnexpectedToken(format!("{:?}", &tokens[begin])));
    }

    // statements begin

    begin += 1;

    if begin >= length {
        error!("unexpected token end. expected an instruction or a new line at ({})", begin);
        return Err(ConditionalBlockParseError::UnexpectedEnd);
    }

    if tokens[begin] == Token::NewLine {
        // block

        begin += 1;

        if begin >= length {
            error!("unexpected token end at ({}). expected a statement", begin);
            return Err(ConditionalBlockParseError::UnexpectedEnd);
        }

        let (if_block, reached) = parse_conditional_statement_block(tokens, begin)
            .map_err(|e| ConditionalBlockParseError::StatementParseError(e.to_string()))?;

        begin = reached + 1;

        if begin >= length {
            error!("unexpected token end at ({}). expected 'end' or 'else'", begin);
            return Err(ConditionalBlockParseError::UnexpectedEnd);
        }

        if tokens[begin] == Token::Keyword(Keyword::Else) {
            let peek_next = begin + 1;

            if peek_next >= length {
                error!("unexpected token end at ({}). expected 'if' or a new line", peek_next);
                return Err(ConditionalBlockParseError::UnexpectedEnd);
            }

            if tokens[peek_next] == Token::NewLine {
                let peek_next = peek_next + 1;

                if peek_next >= length {
                    error!("unexpected token end at ({}). expected 'end' or a statement", peek_next);
                    return Err(ConditionalBlockParseError::UnexpectedEnd);
                }

                let (else_block, reached) = parse_conditional_statement_block(tokens, peek_next)
                    .map_err(|e| ConditionalBlockParseError::StatementParseError(e.to_string()))?;

                let mut next = reached + 1;

                if next >= length {
                    error!("unexpected token end at ({}). expected 'end'", next);
                    return Err(ConditionalBlockParseError::UnexpectedEnd);
                }

                if tokens[next] != Token::Keyword(Keyword::End) {
                    error!("unexpected token at ({}). expected 'end'", next);
                    return Err(ConditionalBlockParseError::UnexpectedToken(format!("{:?}", &tokens[next])));
                }

                next += 1;

                if tokens[next] != Token::Keyword(Keyword::If) {
                    error!("unexpected token at ({}). expected 'if'", next);
                    return Err(ConditionalBlockParseError::UnexpectedToken(format!("{:?}", &tokens[next])));
                }

                return Ok(
                    (
                        ConditionalBlock {
                            condition: cond_expr,
                            if_block,
                            else_block: Some(ElseConditionalBlock::Else(else_block))
                        },

                        next
                    )
                );
            }
        
            if tokens[peek_next] != Token::Keyword(Keyword::If) {
                error!("unexpected token at ({}). expected 'if'", peek_next);
                return Err(ConditionalBlockParseError::UnexpectedToken(format!("{:?}", &tokens[peek_next])));
            }

            let (elseif_block, elseif_reached) = parse_condition(tokens, peek_next)?;

            return Ok(
                (
                    ConditionalBlock {
                        condition: cond_expr,
                        if_block,
                        else_block: Some(ElseConditionalBlock::ElseIf(Box::new(elseif_block)))
                    },

                    elseif_reached
                )
            );
        }

        if tokens[begin] != Token::Keyword(Keyword::End) {
            error!("unexpected ({:?}) at ({}). expected 'end'", &tokens[begin], begin);
            return Err(ConditionalBlockParseError::UnexpectedToken(format!("{:?}", &tokens[begin])));
        }
        
        begin += 1;

        if begin >= length {
            error!("unexpected token end at ({}). expected 'if'", begin);
            return Err(ConditionalBlockParseError::UnexpectedToken(format!("{:?}", &tokens[begin])));
        }

        if tokens[begin] != Token::Keyword(Keyword::If) {
            error!("expected 'if' at ({})", begin);
            return Err(ConditionalBlockParseError::UnexpectedToken(format!("{:?}", &tokens[begin])));
        }

        return Ok(
            (
                ConditionalBlock {
                    condition: cond_expr,
                    if_block,
                    else_block: None
                },

                begin
            )
        );
    } else {
        // same-line

        let (if_block, reached) = parse_statement(tokens, begin)
            .map_err(|e| ConditionalBlockParseError::StatementParseError(e.to_string()))?;


        let peek_next = reached + 1;

        if peek_next >= length {
            error!("unexpected token end at ({}). expected 'else' or a new line", begin);
            return Err(ConditionalBlockParseError::UnexpectedEnd);
        }

        if tokens[peek_next] == Token::Keyword(Keyword::Else) {
            let next = peek_next + 1;

            if next >= length {
                error!("unexpected token end at ({}). expected a statement", next);
                return Err(ConditionalBlockParseError::UnexpectedEnd);
            }

            let (else_block, reached) = parse_statement(tokens, next)
                .map_err(|e| ConditionalBlockParseError::StatementParseError(format!("{:?}", e)))?;
        
            let peek_next = reached + 1;

            if peek_next >= length {
                error!("unexpected token end at ({}). expected a new line", begin);
                return Err(ConditionalBlockParseError::UnexpectedEnd);
            }

            if tokens[peek_next] != Token::NewLine {
                error!("expected a new line at ({})", peek_next);
                return Err(ConditionalBlockParseError::UnexpectedToken(format!("{:?}", &tokens[peek_next])));
            }

            return Ok(
                (
                    ConditionalBlock {
                        condition: cond_expr,
                        if_block: Box::new([ if_block ]),
                        else_block: Some(ElseConditionalBlock::Else(Box::new([ else_block ]))),
                    },

                    reached
                )
            );
        }
    
        if tokens[peek_next] == Token::NewLine {
            error!("expected a new line at ({})", peek_next);
            return Err(ConditionalBlockParseError::UnexpectedToken(format!("{:?}", &tokens[peek_next])));
        }
        
        return Ok(
            (
                ConditionalBlock {
                    condition: cond_expr,
                    if_block: Box::new([ if_block ]),
                    else_block: None
                },

                reached
            )
        );
    }
}

fn parse_repeat_header(tokens: &[Token], cursor: usize) -> Result<(RepeatCondition, usize), RepeatHeaderParseError> {
    use RepeatHeaderParseError::*;
    
    debug!("parsing repeat header at ({})", cursor);
    
    if cursor >= tokens.len() {
        error!("unexpected end of tokens at (). expected 'while' or 'with'");
        return Err(UnexpectedEnd);
    }

    let mut next = cursor;

    if tokens[next] == Token::Keyword(Keyword::While) {
        next += 1;

        if next >= tokens.len() {
            error!("unexpected end of tokens at ({}). expected an expression", next);
            return Err(UnexpectedEnd);
        }

        let (cond_expr, reached) = parse_expression(
            tokens, 
            next, 
            0, 
            true
        )?;

        return Ok(
            (
                RepeatCondition::While(cond_expr),
                reached
            )
        );
    }

    if tokens[next] == Token::Keyword(Keyword::With) {
        next += 1;

        if next >= tokens.len() {
            error!("unexpected end of tokens at ({}). expected an identifier", next);
            return Err(UnexpectedEnd);
        }

        let iterator = if let Token::Identifier(i) = &tokens[next] {
            Ok(Rc::clone(i))
        } else {
            error!("unexpected token ({:?}) at ({}). expected an identifier", &tokens[next], next);
            Err(UnexpectedToken)
        }?;

        next += 1;

        if next >= tokens.len() {
            error!("unexpected end of tokens at ({}). expected '=' or 'in'", next);
            return Err(UnexpectedEnd);
        }

        if tokens[next] == Token::Operator(Operator::AssignmentOrEquality) {
            next += 1;

            if next >= tokens.len() {
                error!("unexpected end of tokens at ({}). expectedan expression", next);
                return Err(UnexpectedEnd);
            }

            let (first_expr, reached) = parse_expression(
                tokens, 
                next, 
                0, 
                true
            )?;

            next = reached + 1;

            if next >= tokens.len() {
                error!("unexpected end of tokens at ({}). expected 'to' or 'down'", next);
                return Err(UnexpectedEnd);
            }

            let mut reversed = false;

            if tokens[next] == Token::Keyword(Keyword::To) {
                next += 1;
            } else if tokens[next] == Token::Keyword(Keyword::Down) {
                next += 1;

                reversed = true;

                if next >= tokens.len() {
                    error!("unexpected end of tokens at ({}). expected 'to'", next);
                    return Err(UnexpectedEnd);
                }

                if tokens[next] == Token::Keyword(Keyword::To) {
                    next += 1;
                } else {
                    error!("unexpected token ({:?}) at ({}). expected an expression", &tokens[next], next);
                    return Err(UnexpectedToken);
                }
            } else {
                error!("unexpected token ({:?}) at ({}). expected 'to' or 'down'", &tokens[next], next);
                return Err(UnexpectedToken);
            }

            if next >= tokens.len() {
                error!("unexpected end of tokens at ({}). expected an expression", next);
                return Err(UnexpectedEnd);
            }

            let (second_expr, reached) = parse_expression(
                tokens, 
                next, 
                0, 
                true
            )?;

            return Ok(
                (
                    RepeatCondition::WithNumberRange { 
                        iterator, 
                        begin: first_expr, 
                        end: second_expr, 
                        reversed 
                    },

                    reached
                )
            );
        }

        if tokens[next] == Token::Keyword(Keyword::In) {
            next += 1;

            if next >= tokens.len() {
                error!("unexpected end of tokens at ({}). expected '=' or 'in'", next);
                return Err(UnexpectedEnd);
            }

            let (range_expr, reached) = parse_expression(
                tokens, 
                next, 
                0, 
                true
            )?;

            return Ok(
                (
                    RepeatCondition::WithListRange { 
                        iterator, 
                        range: range_expr 
                    },

                    reached
                )
            );
        }

        error!("unexpected token ({:?}) at ({}). expected '=' or 'in'", &tokens[next], next);
        return Err(UnexpectedToken);
    }

    error!("unexpected token ({:?}) at ({}). expected 'while' or 'with'", &tokens[next], next);
    return Err(UnexpectedToken);
}

fn parse_repeat_statement(tokens: &[Token], cursor: usize) -> Result<(RepeatStatement, usize), RepeatParseError> {
    use RepeatParseError::*;
    
    if cursor >= tokens.len() {
        error!("unexpected end of tokens at ({}). expected 'repeat'", cursor);
        return Err(UnexpectedEnd);
    }

    if tokens[cursor] != Token::Keyword(Keyword::Repeat) {
        error!("unexpected token ({:?}) at ({}). expected 'repeat'", &tokens[cursor], cursor);
        return Err(UnexpectedToken);
    }

    let mut next = cursor + 1;

    if next >= tokens.len() {
        error!("unexpected end of tokens at ({}). expected 'with' or 'while'", next);
        return Err(UnexpectedEnd);
    }

    let (condition, reached) = parse_repeat_header(tokens, next)?;

    next = reached + 1;

    if next >= tokens.len() {
        error!("unexpected end of tokens at ({}). expected 'then'", next);
        return Err(UnexpectedEnd);
    }

    if tokens[next] != Token::Keyword(Keyword::Then) {
        error!("unexpected token ({:?}) at ({}). expected 'then'", &tokens[next], next);
        return Err(UnexpectedToken);
    }

    next += 1;

    if next >= tokens.len() {
        error!("unexpected end of tokens at ({}). expected a statement or a new line", next);
        return Err(UnexpectedEnd);
    }

    while tokens[next] == Token::NewLine {
        next += 1;

        if next >= tokens.len() {
            error!("unexpected end of tokens at ({}). expected a statement or a new line", next);
            return Err(UnexpectedEnd);
        }
    }

    let (block, reached) = parse_repeat_statement_block(tokens, next)?;

    Ok(
        (
            RepeatStatement {
                condition,
                block
            },

            reached
        )
    )
}

/// consumes 'end (iden)'
fn parse_function_block(tokens: &[Token], cursor: usize, name: &str) -> Result<(Box<[Statement]>, usize), FunctionParseError> {
    use FunctionParseError::*;
    
    debug!("parsing a function block at ({})", cursor);

    let mut next = cursor;

    let mut statements = vec![];

    loop {
        if next >= tokens.len() {
            error!("unexpected end of tokens at ({}). expected a new line, statement, or 'end'", next);
            return Err(UnexpectedEnd);
        }

        while tokens[next] == Token::NewLine {
            next += 1;
    
            if next >= tokens.len() {
                error!("unexpected end of tokens at ({}). expected a new line, statement, or 'end'", next);
                return Err(UnexpectedEnd);
            }
        }

        if tokens[next] == Token::Keyword(Keyword::End) {
            let peek = next + 1;

            if peek >= tokens.len() || tokens[peek] == Token::NewLine {
                return Ok(
                    (
                        statements.into(),
                        next
                    )
                );
            }

            if let Token::Identifier(iden) = &tokens[peek] {
                if iden.as_ref() != name {
                    error!("function 'end' identifier does not match with function's name ({:?}) at ({}). expected '{}'", 
                        &tokens[peek], 
                        peek, 
                        name
                    );

                    return Err(UnexpectedToken);
                }
            } else {
                error!("unexpected token ({:?}) at ({}). expected 'repeat'", &tokens[peek], peek);
                return Err(UnexpectedToken);
            }

            return Ok(
                (
                    statements.into(),
                    peek
                )
            );
        }

        debug!("parsing function statement #({})", statements.len() + 1);

        let (statement, reached) = parse_statement(tokens, next)?;

        statements.push(statement);

        next = reached + 1;

        debug!("successfully parsed function statement #({}). reached ({})", statements.len(), next);
    }
}

fn parse_function(tokens: &[Token], cursor: usize) -> Result<(Function, usize), FunctionParseError> {
    use FunctionParseError::*;

    debug!("parsing a function");

    if cursor >= tokens.len() {
        error!("unexpected end of tokens at ({}). expected 'on'", cursor);
        return Err(UnexpectedEnd);
    }

    if tokens[cursor] != Token::Keyword(Keyword::On) {
        error!("unexpected token ({:?}) at ({}). expected 'at'", tokens[cursor], cursor);
        return Err(UnexpectedToken);
    }

    let mut next = cursor + 1;

    if next >= tokens.len() {
        error!("unexpected end of tokens at ({}). expected a function identifier", next);
        return Err(UnexpectedEnd);
    }

    let name = if let Token::Identifier(iden) = &tokens[next] {
        Ok(Rc::clone(iden))
    } else {
        Err(InvalidName)
    }?;

    next += 1;

    if next >= tokens.len() {
        error!("unexpected end of tokens at ({}). expected function parameters or a new line", next);
        return Err(UnexpectedEnd);
    }

    let parameters = if tokens[next] == Token::OpenParenthesis {
        let mut params = vec![];

        while tokens[next] != Token::CloseParenthesis {
            if tokens[next] != Token::Comma && !params.is_empty() {
                error!("unexpected token ({:?}) at ({}). expected a comma", &tokens[next], next);
                return Err(UnexpectedToken);
            }

            next += 1;

            if next >= tokens.len() {
                error!("unexpected end of tokens at ({}). expected a function parameter", next);
                return Err(UnexpectedEnd);
            }
    
            let (param, reached) = parse_variable_declaration(tokens, next)?;

            params.push(param);
    
            next = reached + 1;
    
            if next >= tokens.len() {
                error!("unexpected end of tokens at ({}). expected a function parameter", next);
                return Err(UnexpectedEnd);
            }
        }

        next += 1;

        if next >= tokens.len() {
            error!("unexpected end of tokens at ({}). expected a new line", next);
            return Err(UnexpectedEnd);
        }

        if tokens[next] != Token::NewLine {
            error!("unexpected token ({:?}) at ({}). expected a new line", &tokens[next], next);
            return Err(UnexpectedToken);
        }

        Result::<Vec<Variable>, FunctionParseError>::Ok(params)
    } else {
        let mut params = vec![];

        while tokens[next] != Token::NewLine {
            if tokens[next] != Token::Comma && !params.is_empty() {
                error!("unexpected token ({:?}) at ({}). expected a comma", &tokens[next], next);
                return Err(UnexpectedToken);
            }

            next += 1;

            if next >= tokens.len() {
                error!("unexpected end of tokens at ({}). expected a function parameter", next);
                return Err(UnexpectedEnd);
            }
    
            let (param, reached) = parse_variable_declaration(tokens, next)?;

            params.push(param);
    
            next = reached + 1;
    
            if next >= tokens.len() {
                error!("unexpected end of tokens at ({}). expected a function parameter", next);
                return Err(UnexpectedEnd);
            }
        }

        Ok(params)
    }?;

    next += 1;
    
    let (block, reached) = parse_function_block(tokens, cursor, name.as_ref())?;

    Ok(
        (
            Function {
                name,
                parameters: parameters.into(),
                block
            },

            reached
        )
    )
}

/// consumes the entire token stream
fn parse_script<T: AsRef<[Token]>>(tokens: T) -> Result<Script, ScriptParseError> {
    use ScriptParseError::*;
    use Token::{
        Keyword
    };
    use tokens::Keyword::{
        On,
        Global,
        Property
    };

    debug!("parsing script");
    
    let tokens = tokens.as_ref();
    
    if tokens.is_empty() { return Err(Empty); }
    
    let mut cursor = 0;

    let mut globals = vec![];
    let mut properties = vec![];
    let mut functions = vec![];

    while cursor < tokens.len() {
        match &tokens[cursor] {
            Keyword(k) => match k {
                Global => {
                    if cursor + 1 < tokens.len() {
                        let (mut parsed_globals, reached) = parse_variable_declarations(
                            tokens, 
                            cursor + 1
                        )?;
    
                        globals.append(&mut parsed_globals);
                        cursor = reached;
                    } else {
                        cursor += 1;
                    }
                },

                Property => {
                    if cursor + 1 < tokens.len() {
                        let (mut parsed_properties, reached) = parse_variable_declarations(
                            tokens, 
                            cursor + 1
                        )?;
    
                        properties.append(&mut parsed_properties);
                        cursor = reached;
                    } else {
                        cursor += 1;
                    }
                },
                
                On => {
                    let (parsed_func, reached) = parse_function(tokens, cursor)?;
                
                    functions.push(parsed_func);
                    cursor = reached;
                },

                _ => {  }
            },

            _ => {}
        }
    }

    Ok(Script {
        functions: functions.into(),
        globals: globals.into(),
        properties: properties.into()
    })
}
