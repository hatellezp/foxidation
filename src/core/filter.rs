use std::fmt::{Display, Formatter};
use std::fmt;

pub struct Filter {
    length: usize,
    number_of_ones: usize,
    lower_one: usize,
    upper_one: usize,
    filter_index: usize,
    filter: Vec<bool>,
    // this is for me
    case_counter: (usize, usize, usize, usize),
}

impl Filter {
    pub fn new(length: usize) -> Filter {
        let filter = vec![false; length];

        let number_of_ones: usize = 0;
        let lower_one: usize = 0;
        let upper_one: usize = 0;
        let filter_index: usize = 0;
        let case_counter: (usize, usize, usize, usize) = (0, 0, 0, 0);

        Filter {
            length,
            number_of_ones,
            lower_one,
            upper_one,
            filter_index,
            filter,
            case_counter,
        }
    }

    pub fn len(&self) -> usize {
        self.length
    }

    pub fn noo(&self) -> usize {
        self.number_of_ones
    }

    pub fn lo(&self) -> usize {
        self.lower_one
    }

    pub fn uo(&self) -> usize {
        self.upper_one
    }

    pub fn filter_index(&self) -> usize {
        self.filter_index
    }

    pub fn filter(&self) -> &Vec<bool> {
        &self.filter
    }

    pub fn filter_mut(&mut self) -> &mut Vec<bool> {
        &mut self.filter
    }

    pub fn cc(&self) -> (usize, usize, usize, usize) {
        self.case_counter
    }

    pub fn reset(&mut self) {
        self.filter = vec![false; self.length];
        self.number_of_ones = 0;
        self.lower_one = 0;
        self.upper_one = 0;
        self.filter_index = 0;
    }

    pub fn is_done(&self) -> bool {
        self.number_of_ones == self.length
    }

    pub fn next(&mut self) {
        // returns (new number of ones, new lower one, new upper one)
        // it also modifies the filter

        let total_size = self.length;
        let number_of_ones = self.number_of_ones;
        let lower_one = self.lower_one;
        let upper_one = self.upper_one;

        if total_size != self.number_of_ones {
            // update the filter index
            self.filter_index += 1;

            if number_of_ones == 0 {
                // println!("          case 1");
                self.filter[0] = true;

                self.number_of_ones = 1;
                self.lower_one = 0;
                self.upper_one = 0;
                self.case_counter.0 += 1;
            } else if (total_size - number_of_ones) == lower_one {
                // println!("          case 2");
                let new_number_of_ones = number_of_ones + 1;
                let new_lower_one: usize = 0;
                let new_upper_one: usize = number_of_ones;

                for i in 0..total_size {
                    if i <= new_upper_one {
                        self.filter[i] = true;
                    } else {
                        self.filter[i] = false;
                    }
                }

                self.number_of_ones = new_number_of_ones;
                self.lower_one = new_lower_one;
                self.upper_one = new_upper_one;
                self.case_counter.1 += 1;
            } else if upper_one < (total_size - 1) {
                // println!("          case 3");
                self.filter[upper_one] = false;
                self.filter[upper_one + 1] = true;

                let new_lower_one = if lower_one != upper_one {
                    lower_one
                } else {
                    lower_one + 1
                };
                let new_upper_one = upper_one + 1;

                self.number_of_ones = number_of_ones;
                self.lower_one = new_lower_one;
                self.upper_one = new_upper_one;
                self.case_counter.2 += 1;
            } else {
                // println!("          case 4");
                // we need to find the before to last one in the filter
                let mut zero_index: usize = total_size - 1;
                let mut one_index: usize = total_size - 2;
                let mut ones_before: usize = 2;

                for j in 0..(total_size - 1) {
                    let i = total_size - 2 - j;

                    // count all ones
                    if self.filter[i] {
                        ones_before += 1;
                    }

                    if (!self.filter[i]) && self.filter[i - 1] {
                        zero_index = i;
                        one_index = i - 1;
                        break;
                    }
                }

                // the one index must be set to false
                self.filter[one_index] = false;

                let new_lower_one = if lower_one == one_index {
                    zero_index
                } else {
                    lower_one
                };
                let mut new_upper_one: usize = 0;

                for i in zero_index..total_size {
                    if ones_before > 0 {
                        ones_before -= 1;
                        self.filter[i] = true;

                        if ones_before == 0 {
                            new_upper_one = i;
                        }
                    } else {
                        self.filter[i] = false
                    }
                }

                self.lower_one = new_lower_one;
                self.upper_one = new_upper_one;
                self.case_counter.3 += 1;
            }
        }
    }
}

impl Display for Filter {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let ones: Vec<u8> = self.filter.iter().map(|x| if *x { 1 } else { 0 }).collect();

        let s = format!(
            "Filter<(l: {}, k: {}, d: {}, u: {}), {:?}>",
            self.length, self.number_of_ones, self.lower_one, self.upper_one, &ones
        );

        write!(f, "{}", s)
    }
}



