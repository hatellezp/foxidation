use std::fmt::Result;
use std::fmt::{Display, Formatter};

use crate::mathsymbols::*;
use std::hash::{Hash, Hasher};
use std::ops::Deref;

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
    Equality,
    PartialEquality,
    GlobalEquality,
    And,
    Or,
    Implies,
    Equivalent,
    Exists,
    ForAll,
}

#[derive(Debug, Clone)]
pub enum Literal {
    Var(String),
    Integer(isize),
    Constant(String),
    RelName(String, usize),
    FuncName(String, usize),
    FormName(String, usize),
    Function(Box<Literal>, Vec<Literal>),
}

impl PartialEq for Literal {
    fn eq(&self, other: &Self) -> bool {
        use Literal::*;

        match (self, other) {
            (Var(value1), Var(value2)) => value1 == value2,
            (Integer(value1), Integer(value2)) => value1 == value2,
            (Constant(value1), Constant(value2)) => value1 == value2,
            (RelName(s1, a1), RelName(s2, a2)) => s1 == s2 && a1 == a2,
            (FuncName(s1, a1), FuncName(s2, a2)) => s1 == s2 && a1 == a2,
            (FormName(s1, a1), FormName(s2, a2)) => s1 == s2 && a1 == a2,
            (Function(boxli1, vec1), Function(boxli2, vec2)) => {
                if boxli1 != boxli2 {
                    return false;
                }

                if vec1.len() != vec2.len() {
                    return false;
                }

                for i in 0..vec1.len() {
                    if vec1[i] != vec2[i] {
                        return false;
                    }
                }

                true
            }
            (_, _) => false,
        }
    }
}

impl Eq for Literal {}

impl Hash for Literal {
    fn hash<H: Hasher>(&self, state: &mut H) {
        use Literal::*;

        match self {
            Var(value) => {
                value.hash(state);
                self.typ().hash(state);
            }
            Integer(value) => {
                value.hash(state);
                self.typ().hash(state);
            }
            Constant(value) => {
                value.hash(state);
                self.typ().hash(state);
            }
            RelName(value, arity) => {
                value.hash(state);
                arity.hash(state);
                self.typ().hash(state);
            }
            FuncName(value, arity) => {
                value.hash(state);
                arity.hash(state);
                self.typ().hash(state);
            }
            FormName(value, arity) => {
                value.hash(state);
                arity.hash(state);
                self.typ().hash(state);
            }
            Function(value, literals) => {
                value.hash(state);

                for literal in literals {
                    literal.hash(state);
                }
            }
        }
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Literal::Var(v) => write!(f, "'{}'", *v),
            Literal::Integer(i) => write!(f, "{}", i),
            Literal::Constant(c) => write!(f, "'{}'", *c),
            Literal::RelName(r, _) => write!(f, "{}", *r), //[{}]", *r, a),
            Literal::FuncName(r, _) => write!(f, "{}", *r), //[{}]", *r, a),
            Literal::FormName(r, _) => write!(f, "{}", *r),
            Literal::Function(a, others) => write!(
                f,
                "{}({})",
                a,
                others
                    .iter()
                    .map(|x| format!("{}", x))
                    .collect::<Vec<String>>()
                    .join(",")
            ),
        }
    }
}

impl Literal {
    pub fn nvariable(v: &str) -> Literal {
        Literal::Var(v.to_string())
    }
    pub fn ninteger(v: isize) -> Literal {
        Literal::Integer(v)
    }
    pub fn nconstant(v: &str) -> Literal {
        Literal::Constant(v.to_string())
    }
    pub fn nrelname(v: &str, a: usize) -> Literal {
        Literal::RelName(v.to_string(), a)
    }
    pub fn nfuncname(v: &str, a: usize) -> Literal {
        Literal::FuncName(v.to_string(), a)
    }
    pub fn nformname(v: &str, a: usize) -> Literal {
        Literal::FormName(v.to_string(), a)
    }

    pub fn nfunction(func_name: &Literal, literals: Vec<Literal>) -> Option<Literal> {
        let there_are_higher_symbols = literals.iter().any(|x| x.deref().is_higher_symbol());

        match (func_name, there_are_higher_symbols) {
            (Literal::FuncName(_, arity), false) => {
                if literals.len() == *arity {
                    Some(Literal::Function(Box::new(func_name.clone()), literals))
                } else {
                    None
                }
            }
            (_, _) => None,
        }
    }

    pub fn typ(&self) -> Type {
        use Literal::*;

        match self {
            Var(_) => Type::Variable,
            Integer(_) => Type::Integer,
            Constant(_) => Type::Constant,
            RelName(_, _) => Type::RelName,
            FuncName(_, _) => Type::FuncName,
            Function(_, _) => Type::Function,
            FormName(_, _) => Type::FormName,
        }
    }

    pub fn vec_of_literals_to_str(v: &[Literal]) -> String {
        let literals: Vec<String> = v.iter().map(|x| format!("{}", x)).collect::<Vec<String>>();
        literals.join(",")
    }

    pub fn is_lower_symbol(&self) -> bool {
        matches!(
            self,
            Literal::Var(_) | Literal::Constant(_) | Literal::Integer(_)
        )
    }

    pub fn is_higher_symbol(&self) -> bool {
        !self.is_lower_symbol()
    }

    pub fn arity(&self) -> usize {
        match self {
            Literal::Var(_)
            | Literal::Constant(_)
            | Literal::Integer(_)
            | Literal::Function(_, _) => 0,
            Literal::RelName(_, a) => *a,
            Literal::FuncName(_, a) => *a,
            Literal::FormName(_, a) => *a,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Expression {
    Relation(Literal, Vec<Literal>),
    Definition(Literal, Vec<Literal>, Box<Expression>),
    BasicEquality(Literal, Literal),
    PartialEquality(Literal, Box<Expression>),
    GeneralEquality(Box<Expression>, Box<Expression>),
    And(Vec<Expression>),
    Or(Vec<Expression>),
    Implies(Box<Expression>, Box<Expression>),
    Equivalent(Box<Expression>, Box<Expression>),
    Exists(Vec<Literal>, Box<Expression>),
    ForAll(Vec<Literal>, Box<Expression>),
}

impl Display for Expression {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Expression::Relation(name, literals) => {
                write!(f, "{}({})", name, Literal::vec_of_literals_to_str(literals))
            },
            Expression::Definition(literal, literals, expression) => {
                let vars = literals.iter().map(|x| format!("{}", x)).collect::<Vec<String>>().join(",");

                write!(f, "{}({}) = {}", literal, vars, expression.deref())
            },
            Expression::BasicEquality(a, b) => write!(f, "{} = {}", a, b),
            Expression::PartialEquality(a, b) => write!(f, "{} = {}", a, b.deref()),
            Expression::GeneralEquality(a, b) => write!(f, "{} = {}", a.deref(), b.deref()),
            Expression::And(expressions) | Expression::Or(expressions) => {
                let ands = expressions
                    .iter()
                    .map(|x| format!("{}", x))
                    .collect::<Vec<String>>();

                let separator = match self {
                    Expression::And(_) => format!(" {} ", AND_CHAR),
                    Expression::Or(_) => format!(" {} ", OR_CHAR),
                    _ => panic!("cannot be here !"),
                };

                write!(f, "{}", ands.join(&separator))
            }
            Expression::Implies(a, b) => write!(f, "{} {} {}", a, IMPLIES_RIGHT_CHAR, b),
            Expression::Equivalent(a, b) => write!(f, "{} {} {}", a, EQUIVALENT_CHAR, b),
            Expression::Exists(literals, expression) | Expression::ForAll(literals, expression) => {
                let vars = Literal::vec_of_literals_to_str(literals);

                let quantifier = match self {
                    Expression::Exists(_, _) => EXISTS_CHAR,
                    Expression::ForAll(_, _) => FORALL_CHAR,
                    _ => panic!("cannot be here !"),
                };

                write!(f, "{} {} {}", quantifier, vars, expression)
            }
        }
    }
}

impl Expression {
    pub fn nrelation(rel_name: &Literal, literals: &[Literal]) -> Option<Expression> {
        let there_are_higher_symbols = literals.iter().any(|x| x.is_higher_symbol());

        match (&rel_name, there_are_higher_symbols) {
            (Literal::RelName(_, arity), false) => {
                if literals.len() == *arity {
                    Some(Expression::Relation(rel_name.clone(), Vec::from(literals)))
                } else {
                    None
                }
            }
            (_, _) => None,
        }
    }

    pub fn ndefinition(name: &Literal, vars: &[Literal], expression: Expression) -> Expression {
        Expression::Definition(name.clone(), Vec::from(vars), Box::new(expression))
    }

    pub fn npartialequality(a: &Literal, b: Expression) -> Expression {
        Expression::PartialEquality(a.clone(), Box::new(b))
    }

    pub fn ngeneralequality(a: Expression, b: Expression) -> Expression {
        Expression::GeneralEquality(Box::new(a), Box::new(b))
    }

    pub fn nand(expressions: Vec<Expression>) -> Expression {
        Expression::And(expressions)
    }

    pub fn nor(expressions: Vec<Expression>) -> Expression {
        Expression::Or(expressions)
    }

    pub fn nequality(a: &Literal, b: &Literal) -> Expression {
        Expression::BasicEquality(a.clone(), b.clone())
    }

    pub fn nimplies(a: Expression, b: Expression) -> Expression {
        Expression::Implies(Box::new(a), Box::new(b))
    }

    pub fn nequivalent(a: Expression, b: Expression) -> Expression {
        Expression::Equivalent(Box::new(a), Box::new(b))
    }

    pub fn nforall(literals: &[Literal], expression: Expression) -> Expression {
        Expression::ForAll(Vec::from(literals), Box::new(expression))
    }

    pub fn nexists(literals: &[Literal], expression: Expression) -> Expression {
        Expression::Exists(Vec::from(literals), Box::new(expression))
    }
}
