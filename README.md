## Description
This executable/library should do mainly two things:
* a boolean satisfiability solver (not the best, but not naive either)
* a reasoner for the [Guarded Fragment](https://en.wikipedia.org/wiki/Guarded_logic) of First Order Logic

### Syntax

The syntax is fairly simple, files can have any extension. You must declare all of your symbols
before use:
``` 
relation: R,0;
relation: S,1;
relation: Other_relation,2;
function: func_a_function,1;
```
Here we declare **R** as a relation symbol of arity 0, **Other_relation** of arity 2 and the 
funciton **func_a_function** of arity 1.

Something to note:
* *all* statements end by a semicolon: ";" ;
* relation symbols begin *always* by an upper letter;
* function symbols *always* have the prefix **func_**;
* variables *always* have the prefix **var_**;
* constants *always* have the prefix **const_**; and
* number must be atomic: "333333" is ok, "333_333" is not.

After that you can define almost anything that is correct in first order logic:
``` 
R() implies Other_relation(2,var_x);
f(4) = f(const_a);
R() IMPLIES R();
Other_relation(const_c, var_y) or true;
forall var_z, var_other_var Other_relation(var_z, var_other_var) implies NOT (var_z = var_other_var);
```

Connectives are **not** case sensitive: "implies" and "IMPLIES" are the same.
The basic values "true" and "FALSE" can be used.
You have an order of precedence for the operators:
* first level:
  * relation statements: ```Other_relation(2, const_c)```;
  * equality statements: ```var_x = const_a_constant```;
  * true and false statements: ```TRUE``` or ```false```;
* second level: 
  * not expressions: ```not (var_x = 2)```;
* third level:
  * and expressions: ```R() and S(2)```;
* fourth level:
  * or expressions: ```false or R()```;
* fifth level:
  * equivalence statements: ```S(const_a) EQUIVALENT S(const_b)```;
* sixth level:
  * implication statements: ```R() implies not R()```;
* seventh level:
  * existential expressions: ```exists var_x S(var_x)```;
  * universal expressions: ```FORALL var_x, var_y Other_relation(var_x, var_y) implies Other_relation(var_y, var_x)```;
  
This precedence level implies that ```R() and S(1) or not S(4)``` is in fact equivalent
to ```(R() and S(1)) or (not S(4))```. You can **of course** bypass the precedence
level by using parenthesis: ```R() and (S(1) or not S(4))```.

### Boolean Satisfiability

For the moment boolean satsifiability is implemented using a naive brute force
prover. You can declare your file in this way for example:
``` 
relation: R,0;
relation: T,0;
relation: S,0;

forall var_x, var_y var_x = var_y;

R() or not R();
not S() or S();

R() implies T();
T() implies ((T() and S()) or R())
```

Note that:
* **ONLY** relations and boolean connectives can be used in boolean formulas;
* **All** relations must be of arity **0**.

You have two possible ways of finding satisfiability, a silent one to find **satisfiability**:

```./foxidation --filename test_sat4.txt --bool-sat --silent```

You should get:
```commandline
===============================================================
= Welcome to the revolutionary foxidation (under development) =
= The next generation first order logic reasoner              =
===============================================================



------------------------
| expression: R() ⋁ ¬R()
| is satisfiable?: true
------------------------
------------------------
| expression: S() ⋁ ¬S()
| is satisfiable?: true
------------------------
------------------------
| expression: R() ⇒ T()
| is satisfiable?: true
------------------------
---------------------------------------
| expression: T() ⇒ (R() ⋁ (S() ⋀ T()))
| is satisfiable?: true
---------------------------------------
```

Note that the expression ```forall var_x, var_y var_x = var_y;``` is not a boolean
expression and thus is **ignored**.

By not putting the silent ```--silent``` argument you can demand a more verbose
output:
```commandline
===============================================================
= Welcome to the revolutionary foxidation (under development) =
= The next generation first order logic reasoner              =
===============================================================



--------------
| R() ⋁ ¬R() |
--------------
==============================================
| R()         | ¬R()         | R() ⋁ ¬R()    |
----------------------------------------------
| false       | true         | true          |
| true        | false        | true          |
==============================================
----------------------------
| is satisfiable?:   true  |
| is a tautology?:   true  |
| is unsatisfiable?: false |
----------------------------


--------------
| S() ⋁ ¬S() |
--------------
==============================================
| S()         | ¬S()         | S() ⋁ ¬S()    |
----------------------------------------------
| false       | true         | true          |
| true        | false        | true          |
==============================================
----------------------------
| is satisfiable?:   true  |
| is a tautology?:   true  |
| is unsatisfiable?: false |
----------------------------


-------------
| R() ⇒ T() |
-------------
============================================
| R()         | T()         | R() ⇒ T()    |
--------------------------------------------
| false       | false       | true         |
| false       | true        | true         |
| true        | false       | false        |
| true        | true        | true         |
============================================
----------------------------
| is satisfiable?:   true  |
| is a tautology?:   false |
| is unsatisfiable?: false |
----------------------------


-----------------------------
| T() ⇒ (R() ⋁ (S() ⋀ T())) |
-----------------------------
==========================================================================================================
| R()         | S()         | T()         | S() ⋀ T()    | R() ⋁ (S() ⋀ T()) | T() ⇒ (R() ⋁ (S() ⋀ T())) |
----------------------------------------------------------------------------------------------------------
| false       | false       | false       | false        | false             | true                      |
| false       | false       | true        | false        | false             | false                     |
| false       | true        | false       | false        | false             | true                      |
| true        | false       | false       | false        | true              | true                      |
| false       | true        | true        | true         | true              | true                      |
| true        | false       | true        | false        | true              | true                      |
| true        | true        | false       | false        | true              | true                      |
| true        | true        | true        | true         | true              | true                      |
==========================================================================================================
----------------------------
| is satisfiable?:   true  |
| is a tautology?:   false |
| is unsatisfiable?: false |
----------------------------
```

### Guarded Fragment Reasoner

Under development


