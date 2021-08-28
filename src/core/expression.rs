use std::cmp::Ordering;
use std::collections::HashSet;
use std::fmt::Result;
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use std::iter::FromIterator;
use std::ops::Deref;

use colored::{ColoredString, Colorize};

use crate::core::literal::Literal;
use crate::core::types::Type::Equivalence;
use crate::core::types::{ExpressionEval, LiteralEval, Type};
use crate::mathsymbols::*;

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

impl Hash for Expression {
    fn hash<H: Hasher>(&self, state: &mut H) {
        use Expression::*;

        match self {
            True => ("True").hash(state),
            False => ("False").hash(state),
            Relation(relname, literals) => {
                (Type::Relation).hash(state);
                relname.hash(state);

                for literal in literals {
                    literal.hash(state);
                }
            }
            Definition(formname, vars, expr) => {
                (Type::Definition).hash(state);
                formname.hash(state);

                for var in vars {
                    var.hash(state);
                }

                expr.deref().hash(state);
            }
            BasicEquality(a, b) => {
                (Type::BasicEquality).hash(state);

                a.hash(state);
                b.hash(state);
            }
            PartialEquality(a, expr) => {
                (Type::PartialEquality).hash(state);

                a.hash(state);
                expr.deref().hash(state);
            }
            GeneralEquality(expr1, expr2) => {
                (Type::GeneralEquality).hash(state);

                expr1.deref().hash(state);
                expr2.deref().hash(state);
            }
            Not(expr) => {
                (Type::Negation).hash(state);

                expr.deref().hash(state);
            }
            And(exprs) => {
                (Type::Conjunction).hash(state);

                for expr in exprs {
                    expr.hash(state);
                }
            }
            Or(exprs) => {
                (Type::Disjunction).hash(state);

                for expr in exprs {
                    expr.hash(state);
                }
            }
            Implies(expr1, expr2) => {
                (Type::Implication).hash(state);

                expr1.deref().hash(state);
                expr2.deref().hash(state);
            }
            Equivalent(expr1, expr2) => {
                (Type::Equivalence).hash(state);

                expr1.deref().hash(state);
                expr2.deref().hash(state);
            }
            Exists(literals, expr) => {
                (Type::Existential).hash(state);

                for literal in literals {
                    literals.hash(state);
                }

                expr.deref().hash(state);
            }
            ForAll(literals, expr) => {
                (Type::Existential).hash(state);

                for literal in literals {
                    literals.hash(state);
                }

                expr.deref().hash(state);
            }
        }
    }
}

impl PartialEq for Expression {
    fn eq(&self, other: &Self) -> bool {
        use Expression::*;

        match (self, other) {
            (True, True) | (False, False) => true,
            (Relation(li1, lis1), Relation(li2, lis2)) => {
                if li1 == li2 {
                    if lis1.len() == lis2.len() {
                        for i in 0..(lis1.len()) {
                            if lis1.get(i).unwrap() != lis2.get(i).unwrap() {
                                return false;
                            }
                        }

                        true
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
            (BasicEquality(a1, b1), BasicEquality(a2, b2)) => a1 == a2 && b1 == b2,
            (Not(expr1), Not(expr2)) => expr1.deref() == expr2.deref(),
            (PartialEquality(a1, expr1), PartialEquality(a2, expr2)) => a1 == a2 && expr1 == expr2,
            (GeneralEquality(expr11, expr12), GeneralEquality(expr21, expr22)) => {
                expr11 == expr21 && expr12 == expr22
            }
            (Or(exprs1), Or(exprs2)) | (And(exprs1), And(exprs2)) => {
                if exprs1.len() != exprs2.len() {
                    false
                } else {
                    let equal_vectors = default_equality_of_vectors(exprs1, exprs2, exprs1.len());

                    equal_vectors
                }
            }
            (Implies(expr11, expr12), Implies(expr21, expr22))
            | (Equivalent(expr11, expr12), Equivalent(expr21, expr22)) => {
                expr11 == expr21 && expr12 == expr22
            }
            (Exists(lis1, expr1), Exists(lis2, expr2))
            | (ForAll(lis1, expr1), ForAll(lis2, expr2)) => {
                if lis1.len() != lis2.len() {
                    return false;
                }

                let equal_vectors = default_equality_of_vectors(lis1, lis2, lis1.len());

                equal_vectors && (expr1 == expr2)
            }
            (Definition(li1, lis1, expr1), Definition(li2, lis2, expr2)) => {
                li1 == li2
                    && lis1.len() == lis2.len()
                    && default_equality_of_vectors(lis1, lis2, lis1.len())
                    && expr1 == expr2
            }
            (_, _) => false,
        }
    }
}

impl Eq for Expression {}

impl PartialOrd for Expression {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        use Expression::*;
        // False < True < Relation < Basic < Not < Partial < General < Or < And < Implies < Equivalent < Exists < ForAll < Definition

        match (self, other) {
            (False, False) => Some(Ordering::Equal),
            (False, _) => Some(Ordering::Less),
            (_, False) => Some(Ordering::Greater),
            (True, True) => Some(Ordering::Equal),
            (True, _) => Some(Ordering::Less),
            (_, True) => Some(Ordering::Greater),
            (Relation(li1, lis1), Relation(li2, lis2)) => {},
            (Relation(_, _), _) => Some(Ordering::Less),
            (_, Relation(_, _)) => Some(Ordering::Greater),
            (BasicEquality(a1, b1), BasicEquality(a2, b2)) => {},
            (BasicEquality(_, _), _) => Some(Ordering::Less),
            (_, BasicEquality(_, _)) => Some(Ordering::Greater),
            (_, _) => todo!(),
        }
    }
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
            And(_) => Type::Conjunction,
            Or(_) => Type::Conjunction,
            Not(_) => Type::Negation,
            Implies(_, _) => Type::Implication,
            Equivalent(_, _) => Type::Equivalence,
            ForAll(_, _) => Type::Universal,
            Exists(_, _) => Type::Existential,
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
                    (0, Type::Conjunction, _) => format!("{}", TOP_CHAR).green().to_string(),
                    (0, Type::Disjunction, _) => format!("{}", BOT_CHAR).green().to_string(),
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
            Not(a) => a
                .to_pure_propositional()
                .map(|a_pure| Not(Box::new(a_pure))),
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
                    let mut inner_literals = Vec::from(literals);
                    inner_literals.sort();
                    Some(Expression::Relation(rel_name.clone(), inner_literals))
                } else {
                    None
                }
            }
            (_, _) => None,
        }
    }

    pub fn ndefinition(name: &Literal, vars: &[Literal], expression: Expression) -> Expression {
        let mut inner_vars = Vec::from(vars);
        inner_vars.sort();
        Expression::Definition(name.clone(), inner_vars, Box::new(expression))
    }

    pub fn npartialequality(a: &Literal, b: Expression) -> Expression {
        Expression::PartialEquality(a.clone(), Box::new(b))
    }

    pub fn ngeneralequality(a: Expression, b: Expression) -> Expression {
        match a.cmp(&b) {
            Ordering::Less | Ordering::Equal => {
                Expression::GeneralEquality(Box::new(a), Box::new(b))
            }
            Ordering::Greater => Expression::GeneralEquality(Box::new(b), Box::new(a)),
        }
    }

    pub fn nnot(a: Expression) -> Expression {
        Expression::Not(Box::new(a))
    }

    pub fn nand(mut expressions: Vec<Expression>) -> Option<Expression> {
        match expressions.iter().any(|x| x.typ() == Type::Definition) {
            true => None,
            _ => {
                expressions.sort();
                Some(Expression::And(expressions))
            }
        }
    }

    pub fn nor(mut expressions: Vec<Expression>) -> Option<Expression> {
        match expressions.iter().any(|x| x.typ() == Type::Definition) {
            true => None,
            _ => {
                expressions.sort();
                Some(Expression::Or(expressions))
            }
        }
    }

    pub fn nbasicequality(a: &Literal, b: &Literal) -> Expression {
        match a.cmp(b) {
            Ordering::Less | Ordering::Equal => Expression::BasicEquality(a.clone(), b.clone()),
            _ => Expression::BasicEquality(b.clone(), a.clone()),
        }
    }

    pub fn nimplies(a: Expression, b: Expression) -> Expression {
        Expression::Implies(Box::new(a), Box::new(b))
    }

    pub fn nequivalent(a: Expression, b: Expression) -> Expression {
        match a.cmp(&b) {
            Ordering::Less | Ordering::Equal => Expression::Equivalent(Box::new(a), Box::new(b)),
            _ => Expression::Equivalent(Box::new(b), Box::new(a)),
        }
    }

    pub fn nforall(literals: &[Literal], expression: Expression) -> Expression {
        let mut inner_literals = Vec::from(literals);

        inner_literals.sort();
        Expression::ForAll(inner_literals, Box::new(expression))
    }

    pub fn nexists(literals: &[Literal], expression: Expression) -> Expression {
        let mut inner_literals = Vec::from(literals);

        inner_literals.sort();
        Expression::Exists(inner_literals, Box::new(expression))
    }

    pub fn default_eval(
        &self,
        literal_eval: &LiteralEval,
        expression_eval: &ExpressionEval,
    ) -> Option<bool> {
        use Expression::*;
        use Literal::*;

        match self {
            True => Some(true),
            False => Some(false),
            Relation(_, _) => expression_eval(self),
            Definition(_, _, _) => None,
            BasicEquality(a, b) => Some(literal_eval(a) == literal_eval(b)),
            PartialEquality(_, _) => None,
            GeneralEquality(a, b) | Implies(a, b) | Equivalent(a, b) => {
                match (expression_eval(a.deref()), expression_eval(b.deref())) {
                    (Some(a_eval), Some(b_eval)) => match self {
                        GeneralEquality(_, _) => Some(a_eval == b_eval),
                        Implies(_, _) => Some(!a_eval || b_eval),
                        Equivalent(_, _) => Some((!a_eval || b_eval) && (a_eval || !b_eval)),
                        _ => unreachable!(),
                    },
                    (_, _) => None,
                }
            }
            Not(a) => expression_eval(a.deref()).map(|x| !x),
            And(exprs) | Or(exprs) => {
                let evaluated = exprs
                    .iter()
                    .map(|x| expression_eval(x))
                    .collect::<Vec<Option<bool>>>();
                let all_some = evaluated.iter().all(|x| x.is_some());

                if !all_some {
                    None
                } else {
                    match self {
                        And(_) => Some(evaluated.iter().fold(true, |accum, x| accum && x.unwrap())),
                        Or(_) => Some(evaluated.iter().fold(false, |accum, x| accum || x.unwrap())),
                        _ => unreachable!(),
                    }
                }
            }
            Exists(_, _) | ForAll(_, _) => None,
        }
    }

    pub fn is_atomic(&self) -> bool {
        match self {
            Expression::Relation(_, _) => true,
            _ => false,
        }
    }

    pub fn subexpressions(&self) -> Vec<Expression> {
        vec![]
    }

    pub fn atoms(&self) -> Option<HashSet<Expression>> {
        use Expression::*;

        match self {
            True | False => None,
            Relation(_, _) => {
                let mut res: HashSet<Expression> = HashSet::new();

                res.insert(self.clone());

                Some(res)
            }
            Definition(_, _, expr) => expr.deref().atoms(),
            BasicEquality(_, _) => {
                let mut res: HashSet<Expression> = HashSet::new();

                res.insert(self.clone());

                Some(res)
            }
            PartialEquality(_, expr) => expr.deref().atoms(),
            GeneralEquality(expr1, expr2) | Implies(expr1, expr2) | Equivalent(expr1, expr2) => {
                let mut atoms1_op = expr1.deref().atoms();
                let mut atoms2_op = expr2.deref().atoms();

                match (atoms1_op.as_mut(), atoms2_op.as_mut()) {
                    (Some(mut atoms1), Some(atoms2)) => {
                        atoms1.extend_from_slice(atoms2);

                        Some(atoms1.clone())
                    }
                    (Some(_), None) => atoms1_op,
                    (None, Some(_)) => atoms2_op,
                    (None, None) => None,
                }
            }
            Not(expr) => expr.deref().atoms(),
            And(exprs) | Or(exprs) => {
                let mut inner_atoms: HashSet<Expression> = HashSet::new();

                for inner_expr in exprs {
                    let inner_atoms_op = inner_expr.atoms();

                    if let Some(some_atoms) = inner_atoms_op {
                        inner_atoms.extend(some_atoms);
                    }
                }

                match inner_atoms.len() {
                    0 => None,
                    _ => Some(inner_atoms),
                }
            }
            Exists(_, expr) | ForAll(_, expr) => expr.deref().atoms(),
        }
    }

    pub fn pure_propositional_satisfiability_naive(&self) -> Option<bool> {
        if !self.is_pure_propositional() {
            None
        } else {
            let self_pure_op = self.to_pure_propositional();

            match &self_pure_op {
                None => panic!("something went wrong when converting to pure propositional, original expression: <{}>", &self),
                Some(self_pure) => {
                    None
                },
            }
        }
    }
}

pub fn default_equality_of_vectors<T: PartialEq + Eq>(v1: &[T], v2: &[T], length: usize) -> bool {
    for i in 0..length {
        if v1.get(i).unwrap() != v2.get(i).unwrap() {
            return false;
        }
    }

    true
}
