use crate::core::expression::Expression;
use crate::core::literal::Literal;

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
            _ => panic!("ERROR: attempt to unwrap error!"),
        }
    }

    pub fn unwrap_as_ref(&self) -> &T {
        match self {
            Result::Ok(a) => a,
            _ => panic!("ERROR: attempt to unwrap error!"),
        }
    }
}

#[derive(Debug, Eq, PartialEq, Clone, Hash)]
pub enum Grounded {
    Word(String),
    Number(isize),
    Undefined,
}

pub type LiteralEval = dyn Fn(&Literal) -> Grounded;
pub type ExpressionEval = dyn Fn(&Expression) -> Option<bool>;
