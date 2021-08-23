use std::collections::HashSet;
use std::fs;
use std::hash::Hash;

use pest::iterators::Pair;
use pest::Parser;

use crate::core::symbols::Type;
use crate::core::symbols::Type::Exists;
use crate::core::symbols::{Expression, Literal};

#[derive(Parser)]
#[grammar = "parser/grammar.pest"]
pub struct GrammarParser;

// TODO: see when you can return an empty vector

pub fn parse_file(file: &str) -> (HashSet<Literal>, Vec<Expression>) {
    fn parse_statement(
        pair: Pair<Rule>,
        context: &mut HashSet<Literal>,
    ) -> (Vec<Literal>, Vec<Expression>) {
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
                (vec![new_literal], vec![])
            }
            // these rules cannot be accessed directly
            Rule::relation_name | Rule::lower_word | Rule::function_name | Rule::formula_name => {
                unreachable!()
            }
            Rule::variable_name => {
                let name = pair.into_inner().next().unwrap().as_str();

                let new_literal = Literal::nvariable(name);

                context.insert(new_literal.clone());
                (vec![new_literal], vec![])
            }
            Rule::constant_name => {
                let name = pair.into_inner().next().unwrap().as_str();

                let new_literal = Literal::nconstant(name);

                context.insert(new_literal.clone());
                (vec![new_literal], vec![])
            }
            Rule::variable_constant_periods | Rule::constant_periods | Rule::variable_periods => {
                let mut inners = pair.into_inner();

                let mut all_literals: Vec<Literal> = Vec::new();

                for pair in inners {
                    let (literals, _) = parse_statement(pair, context);
                    all_literals.extend(literals);
                }

                (all_literals, vec![])
            }
            Rule::relation_declaration => {
                let mut inners = pair.into_inner();

                let name = inners.next().unwrap().as_str();
                let arity = inners.next().unwrap().as_str().parse::<usize>().unwrap();

                let new_literal = Literal::nrelname(name, arity);

                context.insert(new_literal.clone());
                (vec![new_literal], vec![])
            }
            Rule::function_declaration => {
                let mut inners = pair.into_inner();

                let name = inners.next().unwrap().as_str();
                let arity = inners.next().unwrap().as_str().parse::<usize>().unwrap();

                let new_literal = Literal::nfuncname(name, arity);

                context.insert(new_literal.clone());
                (vec![new_literal], vec![])
            }
            Rule::constant_declaration => {
                let mut inners = pair.into_inner();

                let name = inners.next().unwrap().as_str();
                let value = inners.next().unwrap().as_str().parse::<isize>().unwrap();

                let new_constant = Literal::nconstant(name);
                let new_integer = Literal::Integer(value);

                let new_expression =
                    Expression::BasicEquality(new_constant.clone(), new_integer.clone());

                context.insert(new_constant.clone());
                context.insert(new_integer.clone());
                (vec![new_integer, new_constant], vec![new_expression])
            }
            Rule::function_statement => {
                let pair_str = pair.as_str();
                let mut inners = pair.into_inner();

                let name = inners.next().unwrap().as_str();

                let mut literals: Vec<Literal> = Vec::new();

                for inner_pair in inners {
                    let (inner_literals, _) = parse_statement(inner_pair, context);

                    literals.extend_from_slice(&inner_literals);
                    context.extend(inner_literals);
                }

                // now verify
                for literal in context.iter() {
                    if literal.name() == name
                        && literal.arity() == literals.len()
                        && literal.typ() == Type::FuncName
                    {
                        let new_literal_op = Literal::nfunction(literal, literals);

                        if let Some(new_literal) = new_literal_op {
                            return (vec![new_literal], vec![]);
                        } else {
                            return (vec![], vec![]);
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

                // TODO: is this enough ???
                parse_statement(next_statement, context)
            }
            Rule::term_tuple => {
                let mut inners = pair.into_inner();

                let mut tuple: Vec<Literal> = Vec::new();

                for inner_pair in inners {
                    let (literals, _) = parse_statement(inner_pair, context);

                    tuple.push(literals[0].clone());
                    context.extend(literals)
                }

                (tuple, vec![])
            }
            Rule::equality_statement => {
                let mut inners = pair.into_inner();

                let term1 = inners.next().unwrap();
                let term2 = inners.next().unwrap();

                let (mut literals1, _) = parse_statement(term1, context);
                let (literals2, _) = parse_statement(term2, context);

                let new_expression =
                    Expression::nequality(literals1.get(0).unwrap(), literals2.get(0).unwrap());

                context.insert(literals1[0].clone());
                context.insert(literals2[0].clone());

                literals1.extend(literals2);
                (literals1, vec![new_expression])
            }
            Rule::relation_statement => {
                let pair_str = pair.as_str();
                let mut inners = pair.into_inner();

                let name = inners.next().unwrap().as_str();

                let (terms, _) = parse_statement(inners.next().unwrap(), context);

                // now terms have exactly the number of terms necessary
                for literal in context.iter() {
                    if literal.typ() == Type::RelName
                        && literal.name() == name
                        && literal.arity() == terms.len()
                    {
                        // good place, we create the relation statement

                        let new_expression_op = Expression::nrelation(literal, &terms);

                        if let Some(new_expression) = new_expression_op {
                            return (terms, vec![new_expression]);
                        } else {
                            return (vec![], vec![]);
                        }
                    } else if literal.typ() == Type::RelName
                        && literal.name() == name
                        && literal.arity() != terms.len()
                    {
                        panic!("relation '{}' declared with arity '{}' and statement of arity '{}': <{}>", name, literal.arity(), terms.len(), pair_str)
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

                // you should have found the arity at this point otherwise panic !!
                if arity.is_none() {
                    panic!(
                        "relation '{}' not declared! cannot add statements ! <{}>",
                        name, pair_str
                    )
                }
                let arity = arity.unwrap();
                let relname = relname.unwrap();

                let mut expressions: Vec<Expression> = Vec::new();

                for inner_pair in inners {
                    let (tuple, _) = parse_statement(inner_pair, context);

                    if tuple.len() != arity {
                        panic!("tuple {:?} has arity '{}', but relation '{}' was declared with arity '{}'!! <{}>", &tuple, tuple.len(), name, arity, pair_str)
                    } else {
                        let new_expression = Expression::nrelation(&relname, &tuple);
                        expressions.push(new_expression.unwrap());
                    }
                }

                (vec![], expressions)
            }
            Rule::true_expression => (vec![], vec![Expression::ntrue()]),
            Rule::false_expression => (vec![], vec![Expression::nfalse()]),
            Rule::forall_expression => {
                let mut inners = pair.into_inner();

                let (vars, _) = parse_statement(inners.next().unwrap(), context);
                let (_, expressions) = parse_statement(inners.next().unwrap(), context);

                let new_expression = Expression::nforall(&vars, expressions[0].clone());
                context.extend(vars.clone());

                // TODO: is this good ???
                (vec![], vec![new_expression])
            }
            Rule::exists_expression => {
                let mut inners = pair.into_inner();

                let (vars, _) = parse_statement(inners.next().unwrap(), context);
                let (_, expressions) = parse_statement(inners.next().unwrap(), context);

                let new_expression = Expression::nexists(&vars, expressions[0].clone());
                context.extend(vars.clone());

                // TODO: is this good ???
                (vec![], vec![new_expression])
            }
            Rule::parenthesis_expression | Rule::basic_expression => {
                let next_statement = pair.into_inner().next().unwrap();

                parse_statement(next_statement, context)
            }
            Rule::not_expression => {
                let mut inners = pair.into_inner();

                let next_statement = inners.next().unwrap();

                match next_statement.as_rule() {
                    Rule::not_literal => {
                        let next_next_statement = inners.next().unwrap();

                        let (_, expressions) = parse_statement(next_next_statement, context);

                        let new_expression = Expression::nnot(expressions[0].clone());

                        (vec![], vec![new_expression])
                    }
                    _ => parse_statement(next_statement, context),
                }
            }
            Rule::and_expression => {
                let mut inners = pair.into_inner();

                let mut expressions: Vec<Expression> = Vec::new();

                for inner_pair in inners {
                    let (_, exprs) = parse_statement(inner_pair, context);

                    expressions.extend(exprs);
                }

                match expressions.len() {
                    0 => panic!("you cannot be here (and expression panicked!)"),
                    1 => (vec![], expressions),
                    _ => {
                        let new_expression = Expression::nand(expressions);

                        (vec![], vec![new_expression])
                    }
                }
            }
            Rule::or_expression => {
                let mut inners = pair.into_inner();

                let mut expressions: Vec<Expression> = Vec::new();

                for inner_pair in inners {
                    let (_, exprs) = parse_statement(inner_pair, context);

                    expressions.extend(exprs);
                }

                match expressions.len() {
                    0 => panic!("you cannot be here (and expression panicked!)"),
                    1 => (vec![], expressions),
                    _ => {
                        let new_expression = Expression::nor(expressions);

                        (vec![], vec![new_expression])
                    }
                }
            }
            Rule::equivalent_expression => {
                let mut inners = pair.into_inner();

                let (_, expr1) = parse_statement(inners.next().unwrap(), context);

                if let Some(inner_pair) = inners.next() {
                    let (_, expr2) = parse_statement(inner_pair, context);

                    let new_expression =
                        Expression::nequivalent(expr1[0].clone(), expr2[0].clone());

                    (vec![], vec![new_expression])
                } else {
                    (vec![], expr1)
                }
            }
            Rule::implies_expression => {
                let mut inners = pair.into_inner();

                let (_, expr1) = parse_statement(inners.next().unwrap(), context);

                if let Some(inner_pair) = inners.next() {
                    let (_, expr2) = parse_statement(inner_pair, context);

                    let new_expression = Expression::nimplies(expr1[0].clone(), expr2[0].clone());

                    (vec![], vec![new_expression])
                } else {
                    (vec![], expr1)
                }
            }
            Rule::expression => {
                let next_statement = pair.into_inner().next().unwrap();

                parse_statement(next_statement, context)
            }
            Rule::expression_definition => {
                // TODO!
                println!("expression definition");
                (vec![], vec![])
            }
            Rule::any_statement => {
                let next_statement = pair.into_inner().next().unwrap();

                parse_statement(next_statement, context)
            }
            Rule::EOI => (vec![], vec![]),
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
                let (_, mut exprs) = parse_statement(any_statement, &mut context);

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

