use std::fmt::Result;
use std::fmt::{Display, Formatter};

use colored::{Colorize};

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
    BasicEquality,
    PartialEquality,
    GeneralEquality,
    Definition,
    Negation,
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
            Literal::Var(v) => write!(f, "'{}'", v.blue()),
            Literal::Integer(i) => write!(f, "{}", i.to_string().blue()),
            Literal::Constant(c) => write!(f, "'{}'", c.blue()),
            Literal::RelName(r, _) => write!(f, "{}", r.red()), //[{}]", *r, a),
            Literal::FuncName(r, _) => write!(f, "{}", r.red()), //[{}]", *r, a),
            Literal::FormName(r, _) => write!(f, "{}", r.red()),
            Literal::Function(a, others) => write!(
                f,
                "{}({})",
                a.deref().to_string().red(),
                others
                    .iter()
                    .map(|x| format!("{}", x).blue().to_string())
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

    pub fn name(&self) -> &str {
        use Literal::*;

        match self {
            Var(s) | Constant(s) | RelName(s, _) | FuncName(s, _) | FormName(s, _) => s,
            Integer(_) => "",
            Function(li_box, _) => li_box.deref().name(),
        }
    }

    pub fn vec_of_literals_to_str(v: &[Literal], formatting: bool) -> String {
        let literals: Vec<String>;

        if formatting {
            literals = v
                .iter()
                .map(|x| format!("{}", x).blue().to_string())
                .collect::<Vec<String>>();
        } else {
            literals = v.iter().map(|x| format!("{}", x)).collect::<Vec<String>>();
        }

        literals.join(",")
    }

    pub fn is_lower_symbol(&self) -> bool {
        matches!(
            self,
            Literal::Var(_) | Literal::Constant(_) | Literal::Integer(_) | Literal::Function(_, _)
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
    True,
    False,
    Relation(Literal, Vec<Literal>),
    Definition(Literal, Vec<Literal>, Box<Expression>),
    BasicEquality(Literal, Literal),
    PartialEquality(Literal, Box<Expression>),
    GeneralEquality(Box<Expression>, Box<Expression>),
    Not(Box<Expression>),
    And(Vec<Expression>),
    Or(Vec<Expression>),
    Implies(Box<Expression>, Box<Expression>),
    Equivalent(Box<Expression>, Box<Expression>),
    Exists(Vec<Literal>, Box<Expression>),
    ForAll(Vec<Literal>, Box<Expression>),
}

impl Display for Expression {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{}", self.to_string_complex(true))
    }
}

impl Expression {
    pub fn typ(&self) -> Type {
        use Expression::*;

        match self {
            True | False => Type::Constant,
            Relation(_, _) => Type::Relation,
            Definition(_, _, _) => Type::Definition,
            BasicEquality(_, _) => Type::BasicEquality,
            PartialEquality(_, _) => Type::PartialEquality,
            GeneralEquality(_, _) => Type::GeneralEquality,
            And(_) => Type::And,
            Or(_) => Type::And,
            Not(_) => Type::Negation,
            Implies(_, _) => Type::Implies,
            Equivalent(_, _) => Type::Equivalent,
            ForAll(_, _) => Type::ForAll,
            Exists(_, _) => Type::Exists,
        }
    }

    pub fn is_complex_expression(&self) -> bool {
        use Expression::*;

        match self {
            True | False | Relation(_, _) | Definition(_, _, _) => false,
            And(exprs) | Or(exprs) => exprs.len() != 1,
            _ => true,
        }
    }

    pub fn to_string_complex(&self, is_top_expression: bool) -> String {
        match self {
            Expression::True => format!("{}", TOP_CHAR).green().to_string(),
            Expression::False => format!("{}", BOT_CHAR).green().to_string(),
            Expression::Relation(name, literals) => {
                let vars = Literal::vec_of_literals_to_str(literals, true);

                format!("{}({})", name.to_string().red().to_string(), vars)
            }
            Expression::Definition(literal, literals, expression) => {
                let vars = Literal::vec_of_literals_to_str(literals, true);

                let expr_string = expression.deref().to_string_complex(false);
                format!(
                    "{}({}) {} {}",
                    literal.to_string().red().to_string(),
                    vars,
                    TRIPLE_BAR_CHAR.to_string().yellow().to_string(),
                    expr_string
                )
            }
            Expression::BasicEquality(a, b) => format!("{} {} {}", a, "=".yellow(), b),
            Expression::PartialEquality(a, b) => {
                format!(
                    "{} {} {}",
                    a,
                    "=".yellow(),
                    b.deref().to_string_complex(false)
                )
            }
            Expression::GeneralEquality(a, b) => format!(
                "{} {} {}",
                a.deref().to_string_complex(false),
                "=".yellow(),
                b.deref().to_string_complex(false)
            ),
            Expression::Not(a) => match a.deref().is_complex_expression() {
                true => format!(
                    "{}({})",
                    NOT.to_string().yellow(),
                    a.deref().to_string_complex(false)
                ),
                false => format!(
                    "{}{}",
                    NOT.to_string().yellow(),
                    a.deref().to_string_complex(false)
                ),
            },
            Expression::And(expressions) | Expression::Or(expressions) => {
                let ands = expressions
                    .iter()
                    .map(|x| x.to_string_complex(false))
                    .collect::<Vec<String>>();

                let separator = match self {
                    Expression::And(_) => format!(" {} ", AND_CHAR).yellow().to_string(),
                    Expression::Or(_) => format!(" {} ", OR_CHAR).yellow().to_string(),
                    _ => panic!("cannot be here !"),
                };

                match (expressions.len(), self.typ(), is_top_expression) {
                    (0, Type::And, _) => format!("{}", TOP_CHAR).green().to_string(),
                    (0, Type::Or, _) => format!("{}", BOT_CHAR).green().to_string(),
                    (1, _, _) => format!("{}", expressions.get(0).unwrap()),
                    (_, _, false) => format!("({})", ands.join(&separator)),
                    (_, _, true) => ands.join(&separator),
                }
            }
            Expression::Implies(a, b) => format!(
                "{} {} {}",
                a.deref().to_string_complex(false),
                IMPLIES_RIGHT_CHAR.to_string().yellow().to_string(),
                b.deref().to_string_complex(false)
            ),
            Expression::Equivalent(a, b) => format!(
                "{} {} {}",
                a.deref().to_string_complex(false),
                EQUIVALENT_CHAR.to_string().yellow().to_string(),
                b.deref().to_string_complex(false)
            ),
            Expression::Exists(literals, expression) | Expression::ForAll(literals, expression) => {
                let vars = Literal::vec_of_literals_to_str(literals, true);

                let quantifier = match self {
                    Expression::Exists(_, _) => EXISTS_CHAR.to_string().magenta().to_string(),
                    Expression::ForAll(_, _) => FORALL_CHAR.to_string().magenta().to_string(),
                    _ => panic!("cannot be here !"),
                };

                format!(
                    "{} {} {}",
                    quantifier,
                    vars,
                    expression.deref().to_string_complex(false)
                )
            }
        }
    }

    /// here a pure propositional expression is any expression with relation
    /// of arities equal to zero and logical connectives,
    /// no constants, no variables, no function symbols and NO quantifiers
    pub fn is_pure_propositional(&self) -> bool {
        use Expression::*;
        use Literal::*;

        match self {
            True | False => true,
            Relation(relname, literals) => match (relname, literals.len()) {
                (RelName(_, _arity), 0) => true,
                (_, _) => false,
            },
            Definition(_, _, _) => false,
            BasicEquality(_, _) | PartialEquality(_, _) | GeneralEquality(_, _) => false,
            Implies(a, b) | Equivalent(a, b) => {
                a.deref().is_pure_propositional() && b.deref().is_pure_propositional()
            }
            ForAll(_, _) | Exists(_, _) => false,
            And(exprs) | Or(exprs) => exprs.iter().all(|x| x.is_pure_propositional()),
            Not(a) => a.deref().is_pure_propositional(),
        }
    }

    pub fn to_pure_propositional(&self) -> Option<Expression> {
        use Expression::*;
        

        match self {
            True => Some(True),
            False => Some(False),
            Relation(relname, _literals) => {
                if relname.arity() == 0 && relname.typ() == Type::RelName {
                    Some(Relation(relname.clone(), vec![]))
                } else {
                    None
                }
            }
            Definition(_, _, _) => None,
            BasicEquality(_, _) | PartialEquality(_, _) | GeneralEquality(_, _) => None,
            Not(a) => a.to_pure_propositional().map(|a_pure| Not(Box::new(a_pure))),
            And(exprs) | Or(exprs) => {
                let exprs_pure = exprs
                    .iter()
                    .map(|x| x.to_pure_propositional())
                    .collect::<Vec<Option<Expression>>>();

                if exprs_pure.iter().any(|x| x.is_none()) {
                    None
                } else {
                    match self {
                        And(_) => Some(And(exprs_pure
                            .iter()
                            .map(|x| x.as_ref().unwrap().clone())
                            .collect::<Vec<Expression>>())),
                        Or(_) => Some(Or(exprs_pure
                            .iter()
                            .map(|x| x.as_ref().unwrap().clone())
                            .collect::<Vec<Expression>>())),
                        _ => unreachable!(),
                    }
                }
            }
            Implies(a, b) => {
                match (
                    a.deref().to_pure_propositional(),
                    b.deref().to_pure_propositional(),
                ) {
                    (Some(a_pure), Some(b_pure)) => {
                        let not_a_pure = Expression::nnot(a_pure);
                        let or_pure_op = Expression::nor(vec![not_a_pure, b_pure]);

                        match or_pure_op {
                            None => None,
                            Some(_) => or_pure_op,
                        }
                    }
                    (_, _) => None,
                }
            }
            Equivalent(a, b) => {
                match (
                    a.deref().to_pure_propositional(),
                    b.deref().to_pure_propositional(),
                ) {
                    (Some(a_pure), Some(b_pure)) => {
                        let not_a_pure = Expression::nnot(a_pure.clone());
                        let not_b_pure = Expression::nnot(b_pure.clone());

                        let not_a_or_b_op = Expression::nor(vec![not_a_pure, b_pure]);
                        let not_b_or_a_op = Expression::nor(vec![not_b_pure, a_pure]);

                        match (not_a_or_b_op, not_b_or_a_op) {
                            (Some(not_a_or_b), Some(not_b_or_a)) => {
                                let and_pure_op = Expression::nand(vec![not_a_or_b, not_b_or_a]);

                                match and_pure_op {
                                    None => None,
                                    Some(_) => and_pure_op,
                                }
                            }
                            (_, _) => None,
                        }
                    }
                    (_, _) => None,
                }
            }
            Exists(_, _) | ForAll(_, _) => None,
        }
    }

    pub fn ntrue() -> Expression {
        Expression::True
    }

    pub fn nfalse() -> Expression {
        Expression::False
    }

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

    pub fn nnot(a: Expression) -> Expression {
        Expression::Not(Box::new(a))
    }

    pub fn nand(expressions: Vec<Expression>) -> Option<Expression> {
        match expressions.iter().any(|x| x.typ() == Type::Definition) {
            true => None,
            _ => Some(Expression::And(expressions)),
        }
    }

    pub fn nor(expressions: Vec<Expression>) -> Option<Expression> {
        match expressions.iter().any(|x| x.typ() == Type::Definition) {
            true => None,
            _ => Some(Expression::Or(expressions)),
        }
    }

    pub fn nbasicequality(a: &Literal, b: &Literal) -> Expression {
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
