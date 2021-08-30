use std::collections::HashSet;

use std::hash::Hash;

use pest::iterators::Pair;
use pest::Parser;

use crate::core::expression::Expression;
use crate::core::literal::Literal;
use crate::core::types::{Result, Type};

#[derive(Parser)]
#[grammar = "parser/grammar.pest"]
pub struct GrammarParser;

// TODO: see when you can return an empty vector

// literals are added to the context when created, no need to add them after
pub fn parse_file(file: &str) -> (HashSet<Literal>, Vec<Expression>) {
    use crate::core::types::Result::*;

    fn parse_statement(
        pair: Pair<Rule>,
        context: &mut HashSet<Literal>,
    ) -> (Option<Vec<Literal>>, Option<Vec<Expression>>) {
        match pair.as_rule() {
            Rule::inner_number | Rule::number => {
                let name = pair
                    .into_inner()
                    .next()
                    .unwrap()
                    .as_str()
                    .parse::<isize>()
                    .unwrap();

                let new_literal = Literal::ninteger(name);

                context.insert(new_literal.clone());
                (Some(vec![new_literal]), None)
            }
            // these rules cannot be accessed directly
            Rule::relation_name | Rule::lower_word | Rule::function_name | Rule::formula_name => {
                unreachable!()
            }
            Rule::variable_name => {
                let name = pair.as_str(); // .split("var_").collect::<Vec<&str>>()[1];

                let new_literal = Literal::nvariable(name);

                context.insert(new_literal.clone());
                (Some(vec![new_literal]), None)
            }
            Rule::constant_name => {
                let name = pair.as_str(); //.split("const_").collect::<Vec<&str>>()[1];

                let new_literal = Literal::nconstant(name);

                context.insert(new_literal.clone());
                (Some(vec![new_literal]), None)
            }
            Rule::variable_constant_periods | Rule::constant_periods | Rule::variable_periods => {
                let inners = pair.into_inner();

                let mut all_literals: Vec<Literal> = Vec::new();

                for inner_pair in inners {
                    let inner_pair_str = inner_pair.as_str();
                    let (literals, _) = parse_statement(inner_pair, context);

                    if literals.is_none() {
                        panic!("parsing panicked here: <{}>", inner_pair_str)
                    }

                    all_literals.extend(literals.unwrap());
                }

                (Some(all_literals), None)
            }
            Rule::relation_declaration => {
                let mut inners = pair.into_inner();

                let name = inners.next().unwrap().as_str();
                let arity = inners.next().unwrap().as_str().parse::<usize>().unwrap();

                let new_literal = Literal::nrelname(name, arity);

                context.insert(new_literal.clone());
                (Some(vec![new_literal]), None)
            }
            Rule::function_declaration => {
                let mut inners = pair.into_inner();

                let name = inners.next().unwrap().as_str(); //.split("func_").collect::<Vec<&str>>()[1];
                let arity = inners.next().unwrap().as_str().parse::<usize>().unwrap();

                let new_literal = Literal::nfuncname(name, arity);

                context.insert(new_literal.clone());
                (Some(vec![new_literal]), None)
            }
            Rule::constant_declaration => {
                let mut inners = pair.into_inner();

                let name = inners.next().unwrap().as_str();
                let value = inners.next().unwrap().as_str().parse::<isize>().unwrap();

                let new_constant = Literal::nconstant(name);
                let new_integer = Literal::Integer(value);

                let new_expression =
                    Expression::BasicEquality(new_constant.clone(), new_integer.clone());

                context.insert(new_constant);
                context.insert(new_integer);

                (None, Some(vec![new_expression]))
            }
            Rule::function_statement => {
                let pair_str = pair.as_str();
                let mut inners = pair.into_inner();

                let name = inners.next().unwrap().as_str();

                let mut literals: Vec<Literal> = Vec::new();

                for inner_pair in inners {
                    let inner_pair_str = inner_pair.as_str();
                    let (inner_literals, _) = parse_statement(inner_pair, context);

                    if inner_literals.is_none() {
                        panic!("parsing panicked at : <{}>", inner_pair_str);
                    }

                    literals.extend(inner_literals.unwrap());
                }

                // now verify
                for literal in context.iter() {
                    if literal.name() == name
                        && literal.arity() == literals.len()
                        && literal.typ() == Type::FuncName
                    {
                        let new_literal_op = Literal::nfunction(literal, literals);

                        if let Result::Ok(new_literal) = new_literal_op {
                            context.insert(new_literal.clone());

                            return (Some(vec![new_literal]), None);
                        } else {
                            panic!("could not create function statement: <{}>", pair_str);
                        }
                    } else if literal.name() == name
                        && literal.arity() != literals.len()
                        && literal.typ() == Type::FuncName
                    {
                        panic!("function '{}' declared with arity '{}' and statement of arity '{}': <{}>", name, literal.arity(), literals.len(), pair_str)
                    }
                }

                panic!("couldn't parse: <{}>, panicking", pair_str);
            }
            Rule::term => {
                let next_statement = pair.into_inner().next().unwrap();

                // TODO: is this enough, yes it is
                parse_statement(next_statement, context)
            }
            Rule::term_tuple => {
                let inners = pair.into_inner();

                let mut tuple: Vec<Literal> = Vec::new();

                for inner_pair in inners {
                    let inner_pair_str = inner_pair.as_str();
                    let (literals, _) = parse_statement(inner_pair, context);

                    if literals.is_none() {
                        panic!("could not parse: <{}>", inner_pair_str)
                    }

                    tuple.push(literals.unwrap()[0].clone());
                }

                (Some(tuple), None)
            }
            Rule::equality_statement => {
                let pair_str = pair.as_str();
                let mut inners = pair.into_inner();

                let term1 = inners.next().unwrap();
                let term2 = inners.next().unwrap();

                let (literals1_op, _) = parse_statement(term1, context);
                let (literals2_op, _) = parse_statement(term2, context);

                match (literals1_op, literals2_op) {
                    (Some(literals1), Some(literals2)) => {
                        let new_expression = Expression::nbasicequality(
                            literals1.get(0).unwrap(),
                            literals2.get(0).unwrap(),
                        );

                        (None, Some(vec![new_expression]))
                    }
                    (_, _) => panic!("could not parse expression: <{}>", pair_str),
                }
            }
            Rule::relation_statement => {
                let pair_str = pair.as_str();
                let mut inners = pair.into_inner();

                let name = inners.next().unwrap().as_str();

                let (terms, _) = parse_statement(inners.next().unwrap(), context);

                if terms.is_none() {
                    panic!("could not parse expression: <{}>", pair_str);
                }

                // now terms have exactly the number of terms necessary
                for literal in context.iter() {
                    if literal.typ() == Type::RelName
                        && literal.name() == name
                        && literal.arity() == terms.as_ref().unwrap().len()
                    {
                        // good place, we create the relation statement

                        let new_expression_op = Expression::nrelation(literal, &terms.unwrap());

                        if let Result::Ok(new_expression) = new_expression_op {
                            return (None, Some(vec![new_expression]));
                        } else {
                            panic!("could not parse expression: <{}>", pair_str);
                        }
                    } else if literal.typ() == Type::RelName
                        && literal.name() == name
                        && literal.arity() != terms.as_ref().unwrap().len()
                    {
                        panic!("relation '{}' declared with arity '{}' and statement of arity '{}': <{}>", name, literal.arity(), terms.as_ref().unwrap().len(), pair_str)
                    }
                }

                panic!("couldn't parse <{}>, panicking", pair_str);
            }
            Rule::relation_extended_statement => {
                let pair_str = pair.as_str();

                let mut inners = pair.into_inner();

                let name = inners.next().unwrap().as_str();

                let mut arity: Option<usize> = None;
                let mut relname: Option<Literal> = None;

                for literal in context.iter() {
                    if literal.name() == name && literal.typ() == Type::RelName {
                        arity = Some(literal.arity());
                        relname = Some(literal.clone());
                        break;
                    }
                }

                if relname.is_none() || arity.is_none() {
                    panic!(
                        "relation '{}' not declared! cannot add statements ! <{}>",
                        name, pair_str
                    )
                }
                let arity = arity.unwrap();
                let relname = relname.unwrap();

                let mut expressions: Vec<Expression> = Vec::new();

                for inner_pair in inners {
                    let inner_pair_str = inner_pair.as_str();
                    let (tuple, _) = parse_statement(inner_pair, context);

                    if tuple.is_none() {
                        panic!("could not parse expression: <{}>", inner_pair_str);
                    }

                    let tuple = tuple.unwrap();

                    if tuple.len() != arity {
                        panic!("tuple {:?} has arity '{}', but relation '{}' was declared with arity '{}'!! <{}>", &tuple, tuple.len(), name, arity, pair_str)
                    } else {
                        let new_expression = Expression::nrelation(&relname, &tuple);

                        if !new_expression.is_ok() {
                            panic!("could not parse expression: <{}>", inner_pair_str);
                        }

                        expressions.push(new_expression.unwrap());
                    }
                }

                (None, Some(expressions))
            }
            Rule::true_expression => (None, Some(vec![Expression::ntrue()])),
            Rule::false_expression => (None, Some(vec![Expression::nfalse()])),
            Rule::forall_expression => {
                let pair_str = pair.as_str();
                let mut inners = pair.into_inner();

                let (vars, _) = parse_statement(inners.next().unwrap(), context);
                let (_, expressions) = parse_statement(inners.next().unwrap(), context);

                if vars.is_none() || expressions.is_none() {
                    panic!("could not parse expression: <{}>", pair_str);
                }

                let new_expression =
                    Expression::nforall(&vars.unwrap(), expressions.unwrap()[0].clone());
                // context.extend(vars.clone());

                // TODO: is this good ???
                (None, Some(vec![new_expression]))
            }
            Rule::exists_expression => {
                let pair_str = pair.as_str();
                let mut inners = pair.into_inner();

                let (vars, _) = parse_statement(inners.next().unwrap(), context);
                let (_, expressions) = parse_statement(inners.next().unwrap(), context);

                if vars.is_none() || expressions.is_none() {
                    panic!("could not parse expression: <{}>", pair_str);
                }

                let new_expression =
                    Expression::nexists(&vars.unwrap(), expressions.unwrap()[0].clone());
                // context.extend(vars.clone());

                // TODO: is this good ???
                (None, Some(vec![new_expression]))
            }
            Rule::parenthesis_expression | Rule::basic_expression => {
                let next_statement = pair.into_inner().next().unwrap();

                parse_statement(next_statement, context)
            }
            Rule::not_expression => {
                let pair_str = pair.as_str();
                let mut inners = pair.into_inner();

                let next_statement = inners.next().unwrap();

                match next_statement.as_rule() {
                    Rule::not_literal => {
                        let next_next_statement = inners.next().unwrap();

                        let (_, expressions) = parse_statement(next_next_statement, context);

                        if expressions.is_none() {
                            panic!("could not parse expression: <{}>", pair_str);
                        }

                        let new_expression = Expression::nnot(expressions.unwrap()[0].clone());

                        (None, Some(vec![new_expression]))
                    }
                    _ => parse_statement(next_statement, context),
                }
            }
            Rule::and_expression => {
                let pair_str = pair.as_str();
                let inners = pair.into_inner();

                let mut expressions: Vec<Expression> = Vec::new();

                for inner_pair in inners {
                    let (_, exprs) = parse_statement(inner_pair, context);

                    if exprs.is_none() {
                        panic!("could not parse expression: <{}>", pair_str);
                    }

                    expressions.extend(exprs.unwrap());
                }

                match expressions.len() {
                    0 => panic!("you cannot be here (and expression panicked!)"),
                    1 => (None, Some(expressions)),
                    _ => {
                        let new_expression_op = Expression::nand(expressions);

                        if !new_expression_op.is_ok() {
                            panic!("could not parse the AND expression: <{}>", pair_str);
                        }

                        (None, Some(vec![new_expression_op.unwrap()]))
                    }
                }
            }
            Rule::or_expression => {
                let pair_str = pair.as_str();
                let inners = pair.into_inner();

                let mut expressions: Vec<Expression> = Vec::new();

                for inner_pair in inners {
                    let (_, exprs) = parse_statement(inner_pair, context);

                    if exprs.is_none() {
                        panic!("could not parse expression: <{}>", pair_str);
                    }

                    expressions.extend(exprs.unwrap());
                }

                match expressions.len() {
                    0 => panic!("you cannot be here (and expression panicked!)"),
                    1 => (None, Some(expressions)),
                    _ => {
                        let new_expression_op = Expression::nor(expressions);

                        if !new_expression_op.is_ok() {
                            panic!("could not parse the OR expression: <{}>", pair_str);
                        }

                        (None, Some(vec![new_expression_op.unwrap()]))
                    }
                }
            }
            Rule::equivalent_expression => {
                let pair_str = pair.as_str();
                let mut inners = pair.into_inner();

                let (_, expr1) = parse_statement(inners.next().unwrap(), context);

                if expr1.is_none() {
                    panic!("could not parse expression: <{}>", pair_str);
                }

                if let Some(inner_pair) = inners.next() {
                    let (_, expr2) = parse_statement(inner_pair, context);

                    if expr2.is_none() {
                        panic!("could not parse expression: <{}>", pair_str);
                    }

                    let new_expression = Expression::nequivalent(
                        expr1.unwrap()[0].clone(),
                        expr2.unwrap()[0].clone(),
                    );

                    (None, Some(vec![new_expression]))
                } else {
                    (None, expr1)
                }
            }
            Rule::implies_expression => {
                let pair_str = pair.as_str();
                let mut inners = pair.into_inner();

                let (_, expr1) = parse_statement(inners.next().unwrap(), context);

                if expr1.is_none() {
                    panic!("could not parse expression: <{}>", pair_str);
                }

                if let Some(inner_pair) = inners.next() {
                    let (_, expr2) = parse_statement(inner_pair, context);

                    if expr2.is_none() {
                        panic!("could not parse expression: <{}>", pair_str);
                    }

                    let new_expression =
                        Expression::nimplies(expr1.unwrap()[0].clone(), expr2.unwrap()[0].clone());

                    (None, Some(vec![new_expression]))
                } else {
                    (None, expr1)
                }
            }
            Rule::expression => {
                let next_statement = pair.into_inner().next().unwrap();

                parse_statement(next_statement, context)
            }
            Rule::expression_definition => {
                // TODO!

                let _pair_str = pair.as_str();
                let mut inners = pair.into_inner();

                let name = inners.next().unwrap().as_str();

                let (vars_op, _) = parse_statement(inners.next().unwrap(), context);

                let (_, expr_op) = parse_statement(inners.next().unwrap(), context);

                match (vars_op, expr_op) {
                    (Some(vars), Some(expr)) => {
                        let all_vars = vars.iter().all(|x| x.typ() == Type::Variable);

                        if all_vars {
                            let arity = vars.len();

                            let form_name = Literal::nformname(name, arity);
                            let new_expression =
                                Expression::ndefinition(&form_name, &vars, expr[0].clone());

                            context.insert(form_name);

                            (None, Some(vec![new_expression]))
                        } else {
                            (None, None)
                        }
                    }
                    (_, _) => (None, None),
                }
            }
            Rule::any_statement => {
                let next_statement = pair.into_inner().next().unwrap();

                parse_statement(next_statement, context)
            }
            Rule::EOI => (None, None),
            _ => {
                println!("{:?} : {}", pair.as_rule(), pair.as_str());
                unreachable!()
            }
        }
    }

    let parsed_file = GrammarParser::parse(Rule::main, file)
        .unwrap()
        .next()
        .unwrap();

    let mut context: HashSet<Literal> = HashSet::new();
    let mut expressions: Vec<Expression> = Vec::new();

    // let mut current_context: HashSet<Literal> = HashSet::new();

    for any_statement in parsed_file.into_inner() {
        match any_statement.as_rule() {
            Rule::any_statement => {
                let (_, exprs) = parse_statement(any_statement, &mut context);

                if exprs.is_none() {
                    continue;
                }

                let mut exprs = exprs.unwrap();

                while !exprs.is_empty() {
                    let expr = exprs.pop().unwrap();
                    expressions.push(expr);
                }
            }
            Rule::EOI => (),
            _ => unreachable!(),
        };
    }

    (context, expressions)
}

pub fn parse_number(p: &Pair<Rule>) -> isize {
    match p.as_rule() {
        Rule::number => p.as_str().parse::<isize>().unwrap(),
        _ => unreachable!(),
    }
}

pub fn parse_word<'a>(p: &'a Pair<Rule>) -> &'a str {
    match p.as_rule() {
        Rule::lower_word
        | Rule::relation_name
        | Rule::function_name
        | Rule::variable_name
        | Rule::constant_name
        | Rule::formula_name => p.as_str(),
        _ => unreachable!(),
    }
}

pub fn parse_word_periods(p: &Pair<Rule>) -> Vec<String> {
    match p.as_rule() {
        Rule::variable_constant_periods | Rule::variable_periods | Rule::constant_periods => (p
            .clone())
        .into_inner()
        .map(|pair| String::from(parse_word(&pair)))
        .collect::<Vec<String>>(),
        _ => unreachable!(),
    }
}
