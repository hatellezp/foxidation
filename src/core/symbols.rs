use std::fmt::Result;
use std::fmt::{Display, Formatter};

use colored::{Colorize, ColoredString};

use crate::mathsymbols::*;

use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::collections::HashSet;
use std::iter::FromIterator;
use std::cmp::Ordering;

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

impl PartialOrd for Literal {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        use Literal::*;

        // Integer < Constant < Var < FuncName < RelName < FormName < Function

        match (self, other) {
            (Integer(i1), Integer(i2)) => i1.partial_cmp(i2),
            (Integer(_), _) => Some(Ordering::Less),
            (_, Integer(_)) => Some(Ordering::Greater),
            (Constant(s1), Constant(s2)) => s1.partial_cmp(s2),
            (Constant(_), _) => Some(Ordering::Less),
            (_, Constant(_)) => Some(Ordering::Greater),
            (Var(s1), Var(s2)) => s1.partial_cmp(s2),
            (Var(_), _) => Some(Ordering::Less),
            (_, Var(_)) => Some(Ordering::Greater),
            (FuncName(s1, i1), FuncName(s2, i2)) => {
                match s1.cmp(s2) {
                    Ordering::Less => Some(Ordering::Less),
                    Ordering::Greater => Some(Ordering::Greater),
                    Ordering::Equal => {
                        if i1 != i2 {
                            panic!("function name duplication!: f1: {}, f2: {}", self, other);
                        } else {
                            Some(Ordering::Equal)
                        }
                    },
                }
            },
            (FuncName(_, _), _) => Some(Ordering::Less),
            (_, FuncName(_, _)) => Some(Ordering::Greater),
            (RelName(s1, i1), RelName(s2, i2)) => {
                match s1.cmp(s2) {
                    Ordering::Less => Some(Ordering::Less),
                    Ordering::Greater => Some(Ordering::Greater),
                    Ordering::Equal => {
                        if i1 != i2 {
                            panic!("relation name duplication!: f1: {}, f2: {}", self, other);
                        } else {
                            Some(Ordering::Equal)
                        }
                    },
                }
            },
            (RelName(_, _), _) => Some(Ordering::Less),
            (_, RelName(_, _)) => Some(Ordering::Greater),
            (FormName(s1, i1), FormName(s2, i2)) => {
                match s1.cmp(s2) {
                    Ordering::Less => Some(Ordering::Less),
                    Ordering::Greater => Some(Ordering::Greater),
                    Ordering::Equal => {
                        if i1 != i2 {
                            panic!("relation name duplication!: f1: {}, f2: {}", self, other);
                        } else {
                            Some(Ordering::Equal)
                        }
                    },
                }
            },
            (FormName(_, _), _) => Some(Ordering::Less),
            (_, FormName(_, _)) => Some(Ordering::Greater),
            (Function(n1, lis1), Function(n2, lis2)) => {
                match n1.deref().partial_cmp(n2.deref()) {
                    Some(Ordering::Less) | Some(Ordering::Greater) =>  n1.deref().partial_cmp(n2.deref()),
                    Some(Ordering::Equal) => {
                        if lis1.len() != lis2.len() {
                            panic!("mismatched arity of fuctions: f1: {}, f2: {}", self, other);
                        } else {
                            let length = lis1.len();
                            for i in 0..length {
                               match lis1.get(i).unwrap().partial_cmp(lis2.get(i).unwrap()) {
                                   Some(Ordering::Less) => Some(Ordering::Less),
                                   Some(Ordering::Greater) => Some(Ordering::Greater),
                                   _ => continue
                               }
                            }

                            Some(Ordering::Equal)
                        }
                    },
                    _ => unreachable!(),
                }
            }
            _ => unreachable!()
        }
    }
}

impl Ord for Literal {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
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

    pub fn nfunction(func_name: &Literal, mut literals:Vec<Literal>) -> Option<Literal> {
        let there_are_higher_symbols = literals.iter().any(|x| x.deref().is_higher_symbol());

        match (func_name, there_are_higher_symbols) {
            (Literal::FuncName(_, arity), false) => {
                if literals.len() == *arity {
                    // always sort !!
                    literals.sort();
                    Some(Literal::Function(Box::new(func_name.clone()), literals))
                } else {
                    None
                }
            }
            (_, _) => None,
        }
    }

    pub fn default_eval(&self) -> Grounded {
        use Literal::*;

        match self {
            Var(s) | Constant(s) => Grounded::Word(s.clone()),
            Integer(i) => Grounded::Number(*i),
            _ => Grounded::Undefined,
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
            },
            Definition(formname, vars, expr) => {
                (Type::Definition).hash(state);
                formname.hash(state);

                for var in vars {
                    var.hash(state);
                }

                expr.deref().hash(state);
            },
            BasicEquality(a, b) => {
                (Type::BasicEquality).hash(state);

                a.hash(state);
                b.hash(state);
            },
            PartialEquality(a, expr) => {
                (Type::PartialEquality).hash(state);

                a.hash(state);
                expr.deref().hash(state);
            },
            GeneralEquality(expr1, expr2) => {
                (Type::GeneralEquality).hash(state);

                expr1.deref().hash(state);
                expr2.deref().hash(state);
            },
            Not(expr) => {
                (Type::Negation).hash(state);

                expr.deref().hash(state);
            },
            And(exprs) => {
                (Type::Conjunction).hash(state);

                for expr in exprs {
                    expr.hash(state);
                }
            },
            Or(exprs) => {
                (Type::Disjunction).hash(state);

                for expr in exprs {
                    expr.hash(state);
                }
            },
            Implies(expr1, expr2) => {
                (Type::Implication).hash(state);

                expr1.deref().hash(state);
                expr2.deref().hash(state);
            },
            Equivalent(expr1, expr2) => {
                (Type::Equivalence).hash(state);

                expr1.deref().hash(state);
                expr2.deref().hash(state);
            },
            Exists(literals, expr) => {
                (Type::Existential).hash(state);

                for literal in literals {
                    literals.hash(state);
                }

                expr.deref().hash(state);
            },
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

impl PartialOrd for Expression {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        use Expression::*;
        // False < True < Relation < Basic < Not < Partial < General < Or < And < Implies < Equivalent < Exists < ForAll < Definition

        match (self, other) {
            (False, False) => Some(Ordering::Equal),
            (False, _) => Some(Ordering::Less),
            (_, False) => Some(Ordering::Greater),
            (_, _) => todo!()
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
            Ordering::Less | Ordering::Equal => Expression::GeneralEquality(Box::new(a), Box::new(b)),
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
            },
        }
    }

    pub fn nor(mut expressions: Vec<Expression>) -> Option<Expression> {
        match expressions.iter().any(|x| x.typ() == Type::Definition) {
            true => None,
            _ => {
                expressions.sort();
                Some(Expression::Or(expressions))
            },
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

    pub fn default_eval(&self, literal_eval: &LiteralEval, expression_eval: &ExpressionEval) -> Option<bool> {
        use Literal::*;
        use Expression::*;

        match self {
            True => Some(true),
            False => Some(false),
            Relation(_, _) => expression_eval(self),
            Definition(_, _, _) => None,
            BasicEquality(a, b) => Some(literal_eval(a) == literal_eval(b)),
            PartialEquality(_, _) => None,
            GeneralEquality(a, b) | Implies(a, b) | Equivalent(a, b) => {
                match (expression_eval(a.deref()), expression_eval(b.deref())) {
                    (Some(a_eval), Some(b_eval)) => {
                        match self {
                            GeneralEquality(_, _) => Some(a_eval == b_eval),
                            Implies(_, _) => Some(!a_eval || b_eval),
                            Equivalent(_, _) => Some((!a_eval || b_eval) && (a_eval || !b_eval)),
                            _ => unreachable!(),
                        }
                    },
                    (_, _) => None,
                }
            },
            Not(a) => expression_eval(a.deref()).map(|x| !x),
            And(exprs) | Or(exprs) => {
                let evaluated = exprs.iter().map(|x| expression_eval(x)).collect::<Vec<Option<bool>>>();
                let all_some = evaluated.iter().all(|x| x.is_some());

                if !all_some {
                    None
                } else {
                    match self {
                        And(_) => Some(evaluated.iter().fold(true, |accum, x| accum && x.unwrap())),
                        Or(_) => Some(evaluated.iter().fold(false, |accum, x| accum || x.unwrap())),
                        _ => unreachable!()
                    }
                }
            },
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
            },
            Definition(_, _, expr) => expr.deref().atoms(),
            BasicEquality(_, _) => {
                let mut res: HashSet<Expression> = HashSet::new();

                res.insert(self.clone());

                Some(res)
            },
            PartialEquality(_, expr) => expr.deref().atoms(),
            GeneralEquality(expr1, expr2) | Implies(expr1, expr2) | Equivalent(expr1, expr2) => {
                let mut atoms1_op = expr1.deref().atoms();
                let mut atoms2_op = expr2.deref().atoms();

                match (atoms1_op.as_mut(), atoms2_op.as_mut()) {
                    (Some(mut atoms1), Some(atoms2)) => {
                        atoms1.extend_from_slice(atoms2);

                        Some(atoms1.clone())
                    },
                    (Some(_), None) => atoms1_op,
                    (None, Some(_)) => atoms2_op,
                    (None, None) => None,
                }
            },
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
                    _ => Some(inner_atoms)
                }
            },
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

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Grounded {
    Word(String),
    Number(isize),
    Undefined,
}

pub type LiteralEval= fn(&Literal) -> Grounded;
pub type ExpressionEval = fn(&Expression) -> Option<bool>;
