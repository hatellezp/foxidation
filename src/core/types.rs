use crate::core::literal::Literal;
use crate::core::expression::Expression;

#[derive(Debug, Hash, Copy, Clone, Eq, PartialEq)]
pub enum Type {
    Variable,
    Integer,
    Constant,
    RelName,
    FuncName,
    FormName,
    Function,
    Relation,
    BasicEquality,
    PartialEquality,
    GeneralEquality,
    Definition,
    Negation,
    Conjunction,
    Disjunction,
    Implication,
    Equivalence,
    Existential,
    Universal,
}

#[derive(Debug, Hash, Clone, Eq, PartialEq)]
pub enum Result<T> {
    Ok(T),
    Err(String),
}

impl<T> Result<T> {
    pub fn is_ok(&self) -> bool {
        matches!(self, Result::Ok(_))
    }

    pub fn unwrap(self) -> T {
        match self {
            Result::Ok(a) => a,
            _ => panic!("ERROR: attempt to unwrap error!")
        }
    }

    pub fn unwrap_as_ref(&self) -> &T {
        match self {
            Result::Ok(a) => a,
            _ => panic!("ERROR: attempt to unwrap error!")
        }
    }
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Grounded {
    Word(String),
    Number(isize),
    Undefined,
}

pub type LiteralEval = fn(&Literal) -> Grounded;
pub type ExpressionEval = fn(&Expression) -> Option<bool>;
