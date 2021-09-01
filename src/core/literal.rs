use crate::core::types;
use crate::core::types::Grounded;
use crate::core::types::Type;
use std::cmp::Ordering;
use std::fmt::{Display, Formatter, Result};
use std::hash::{Hash, Hasher};
use std::ops::Deref;

use colored::{ColoredString, Colorize};

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
            (FuncName(s1, i1), FuncName(s2, i2))
            | (RelName(s1, i1), RelName(s2, i2))
            | (FormName(s1, i1), FormName(s2, i2)) => match s1.cmp(s2) {
                Ordering::Less => Some(Ordering::Less),
                Ordering::Greater => Some(Ordering::Greater),
                Ordering::Equal => {
                    if i1 != i2 {
                        match self {
                            FuncName(_, _) => {
                                panic!("function name duplication!: f1: {}, f2: {}", self, other)
                            }
                            RelName(_, _) => {
                                panic!("relation name duplication!: f1: {}, f2: {}", self, other)
                            }
                            FormName(_, _) => {
                                panic!("formula name duplication!: f1: {}, f2: {}", self, other)
                            }
                            _ => unreachable!(),
                        }
                    } else {
                        Some(Ordering::Equal)
                    }
                }
            },
            (FuncName(_, _), _) => Some(Ordering::Less),
            (_, FuncName(_, _)) => Some(Ordering::Greater),
            (RelName(_, _), _) => Some(Ordering::Less),
            (_, RelName(_, _)) => Some(Ordering::Greater),
            (FormName(_, _), _) => Some(Ordering::Less),
            (_, FormName(_, _)) => Some(Ordering::Greater),
            (Function(n1, lis1), Function(n2, lis2)) => match n1.deref().partial_cmp(n2.deref()) {
                Some(Ordering::Less) | Some(Ordering::Greater) => {
                    n1.deref().partial_cmp(n2.deref())
                }
                Some(Ordering::Equal) => {
                    if lis1.len() != lis2.len() {
                        panic!("mismatched arity of fuctions: f1: {}, f2: {}", self, other);
                    } else {
                        let length = lis1.len();
                        for i in 0..length {
                            match lis1.get(i).unwrap().partial_cmp(lis2.get(i).unwrap()) {
                                Some(Ordering::Less) => return Some(Ordering::Less),
                                Some(Ordering::Greater) => return Some(Ordering::Greater),
                                _ => continue,
                            }
                        }

                        Some(Ordering::Equal)
                    }
                }
                _ => unreachable!(),
            },
        }
    }
}

impl Ord for Literal {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

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

    pub fn nfunction(func_name: &Literal, mut literals: Vec<Literal>) -> types::Result<Literal> {
        let there_are_higher_symbols = literals.iter().any(|x| x.deref().is_higher_symbol());

        match (func_name, there_are_higher_symbols) {
            (Literal::FuncName(_, arity), false) => {
                if literals.len() == *arity {
                    // always sort !!
                    literals.sort();
                    types::Result::Ok(Literal::Function(Box::new(func_name.clone()), literals))
                } else {
                    types::Result::Err(format!("ERROR: mismatched arity between function symbol and terms: symbol: <{}>, arity: <{}>", func_name, arity))
                }
            }
            (Literal::FuncName(_, _), true) => types::Result::Err(format!(
                "ERROR: unvalid terms in the literals: <{:?}>",
                &literals
            )),
            (_, _) => types::Result::Err(format!(
                "ERROR: symbol provided is not a function: <{}>",
                func_name
            )),
        }
    }

    pub fn count_color_characters(&self) -> usize {
        use Literal::*;

        match self {
            RelName(_, _) | FuncName(_, _) | FormName(_, _) => 23,
            Var(_) | Integer(_) | Constant(_) => 23, // TODO: verify that blue counts this
            Function(li, lis) => {
                li.count_color_characters()
                    + lis
                        .iter()
                        .fold(0, |accum, x| accum + x.count_color_characters())
            }
            _ => 5,
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
            Literal::RelName(_, a) | Literal::FuncName(_, a) | Literal::FormName(_, a) => *a,
        }
    }
}
