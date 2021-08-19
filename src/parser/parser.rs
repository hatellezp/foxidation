use std::collections::HashSet;
use std::fs;
use std::hash::Hash;

use pest::iterators::Pair;
use pest::Parser;

use crate::core::symbols::{Expression, Literal};
use crate::core::symbols::Type;

#[derive(Parser)]
#[grammar = "parser/grammar.pest"]
pub struct GrammarParser;

pub fn parse_file(file: &str) -> (HashSet<Literal>, Vec<Expression>) {
    fn parse_statement(pair: Pair<Rule>, context: &mut HashSet<Literal>) -> (Vec<Literal>, Vec<Expression>) {
        match pair.as_rule() {
            Rule::any_statement => {
                let statement = pair.into_inner().next().unwrap();
                {
                    match statement.as_rule() {
                        Rule::relation_declaration => {
                            let mut inners = statement.into_inner();

                            let rule_name: &str = inners.next().unwrap().as_str();
                            let rule_arity: usize =
                                inners.next().unwrap().as_str().parse::<usize>().unwrap();

                            let new_literal = Literal::nrelname(rule_name, rule_arity);

                            let _ = context.insert(new_literal.clone());
                            (vec![new_literal], vec![])
                        }
                        Rule::function_declaration => {
                            let mut inners = statement.into_inner();

                            let function_name: &str = inners.next().unwrap().as_str();
                            let function_arity: usize =
                                inners.next().unwrap().as_str().parse::<usize>().unwrap();

                            let new_literal = Literal::nfuncname(function_name, function_arity);

                            let _ = context.insert(new_literal.clone());
                            (vec![new_literal], vec![])
                        }
                        Rule::constant_declaration => {
                            let mut inners = statement.into_inner();

                            let constant_name: &str = inners.next().unwrap().as_str();
                            let value: isize =
                                inners.next().unwrap().as_str().parse::<isize>().unwrap();

                            let new_literal1 = Literal::nconstant(constant_name);
                            let new_literal2 = Literal::ninteger(value);

                            let new_expression =
                                Expression::nequality(&new_literal1, &new_literal2);

                            let _ = context.insert(new_literal1.clone());
                            let _ = context.insert(new_literal2.clone());
                            (vec![new_literal1, new_literal2], vec![new_expression])
                        }
                        Rule::expression => parse_statement(statement, context),
                        Rule::expression_definition => {
                            let mut inners = statement.into_inner();

                            let formula_name = inners.next().unwrap().as_str();

                            let word_periods = inners.next().unwrap();
                            let word_periods = parse_word_periods(&word_periods);

                            let vars = word_periods.iter().map(|x| Literal::nvariable(x)).collect::<Vec<Literal>>();

                            let formname = Literal::nformname(formula_name, word_periods.len());

                            let expression = inners.next().unwrap();

                            let (mut literals, mut expressions) = parse_statement(expression, context);
                            let new_expression = Expression::ndefinition(&formname, &vars, expressions[0].clone());

                            literals.push(formname.clone());
                            literals.extend(vars);

                            for literal in literals.iter() {
                                let _ = context.insert(literal.clone());
                            }

                            expressions.push(new_expression);

                            (literals, expressions)
                        }
                        _ => unreachable!(),
                    }
                }
            }
            Rule::expression => {
                let next_statement = pair.into_inner().next().unwrap();

                match next_statement.as_rule() {
                    Rule::equality_statement => {
                        let mut inners = next_statement.into_inner();

                        let term1 = inners.next().unwrap();
                        let term2 = inners.next().unwrap();

                        let (mut literals1, _) = parse_statement(term1, context);
                        let (literals2, _) = parse_statement(term2, context);

                        let new_expression =
                            Expression::BasicEquality(literals1[0].clone(), literals2[0].clone());

                        literals1.extend(literals2);

                        for literal in literals1.iter() {
                            let _ = context.insert(literal.clone());
                        }

                        (literals1, vec![new_expression])
                    }
                    Rule::relation_statement => {
                        let statement_as_str = next_statement.as_str();
                        let mut inners = next_statement.into_inner();

                        let name = inners.next().unwrap().as_str();

                        let mut terms: Vec<Literal> = Vec::new();

                        for pair in inners {
                            let (literals, _) = parse_statement(pair, context);

                            // TODO: verify here that literals are the good types
                            terms.extend_from_slice(&literals);
                            context.extend(literals);
                        }

                        for literal in context.iter() {
                           if literal.typ() == Type::RelName && (&format!("{}", literal) == name) && literal.arity() == terms.len() {
                               let new_expression_op = Expression::nrelation(literal, &terms);

                                if let Some(new_expression) = new_expression_op {
                                    return (terms, vec![new_expression])
                                }
                           } else if literal.typ() == Type::RelName && (&format!("{}", literal) == name) && literal.arity() != terms.len() {
                               panic!("relation {} defined with arity {} and statement of arity {} <{}>!!!", name, literal.arity(), terms.len(), statement_as_str)
                           }
                        }

                        panic!("unkown relation name {}!!!", name)
                    },
                    Rule::and_expression => (vec![], vec![]),
                    Rule::or_expression => (vec![], vec![]),
                    Rule::implies_expression => (vec![], vec![]),
                    Rule::equivalent_expression => (vec![], vec![]),
                    Rule::forall_expression => (vec![], vec![]),
                    Rule::exists_expression => (vec![], vec![]),
                    _ => unreachable!(),
                }
            }
            Rule::term => {
                let next_statement = pair.into_inner().next().unwrap();

                match next_statement.as_rule() {
                    Rule::variable_name => {
                        let name = next_statement.as_str();
                        let new_literal = Literal::nvariable(name);

                        let _  = context.insert(new_literal.clone());

                        (vec![new_literal], vec![])
                    }
                    Rule::constant_name => {
                        let name = next_statement.as_str();
                        let new_literal = Literal::nconstant(name);

                        let _ = context.insert(new_literal.clone());

                        (vec![new_literal], vec![])
                    }
                    Rule::number => {
                        let name = next_statement.as_str().parse::<isize>().unwrap();
                        let new_literal = Literal::ninteger(name);

                        let _ = context.insert(new_literal.clone());

                        (vec![new_literal], vec![])
                    }
                    Rule::function_statement => {
                        // TODO
                        (vec![], vec![])
                    }
                    _ => unreachable!(),
                }
            }
            _ => unreachable!(),
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



