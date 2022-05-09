# DPLLT

[![Code style: black](https://img.shields.io/badge/code%20style-black-000000.svg)](https://github.com/psf/black)


## Overview
A python implementation of DPLLT solver for determining satisfiability of SMT
problems. The implementation provides a SAT solver using CDCL logic,
BCP (also known as Unit Propagation) deduction and DLIS decision heuristic,
in addition to 2 implemented theories - a TQ theory and UF theory.
The DPLLT solver uses the lazy approach to combine the SAT solver and the
theories solver. In addition, the repository provides a parser to 
allow multiple input formats and boolean transformation methods such as nnf,
tseitin, etc. You can either use the DPLLT solver as a whole unit or use
specific components individually. 

## Parser
The solvers provided accept formulas represented as a tree of logical blocks
operations and literals for the solvers to understand the relations between
each of the formula's atoms. 

For example: (x -> y) | (!x)
translates to
<br>
<p align=center>
<img src="https://github.com/jyuv/DPLLT/blob/main/assets/logical_tree.png?raw=true">
</p>
<br>
The parser converts strings like the one above to a tree of logical blocks
which is given to the solvers as inputs. Therefore the user can either 
create formulas with the logical blocks directly or write the formulas as
strings and use the parser to convert them

```python
from parsing.logical_blocks import Var, Negate, Imply, Or
from parsing.parse import Parser

# Method 1 - using logical blocks directly
x = Var("x")
y  = Var("y")
formula = Or(Imply(x, y), Negate(x))

# Method 2 - write as string and use parser
parser = Parser()
formula_str = "(x -> y) | (!x)"
formula = parser.parse(formula_str)
```

## Boolean Transformations
Conventional SAT solvers operate on CNF formulas because their form allows for
convenient workflow in which we need to satisfy all clauses and a clause is
SAT if at least one of its contained literals is True.
The repository provides a variety of boolean transformations that are used as 
step stones for converting a general form's formula to a CNF form. The
transformations provided include NNF, CNF, and tseitin, while also providing
a method for translating a CNF formula represented as a logical blocks tree
to a more compact form - A list of sets of ints, where each set represents a
clause and each literal of the CNF formula is mapped to an int such that 
for every literal l mapped to i, the negation of l i mapped to -i. 
The compact format is the one used internally by the solvers to represent the
formulas.

## SAT Solver
The SAT solver implemented is using several techniques to try to reduce
the search path for this NP problem:
1. It implements an implication graph to use the CDCL 
(conflict-driven clause learning) technique to derive bad paths from a conflict
and to skip them.

2. Always try to first run BCP (boolean constraint propagation, also known as
UP / unit propagation) to deduce trivial assignments from clauses, making the
search path much shorter and quicker. Experiments suggest that this efficient
method is usually responsible for 80-90% of the assignments the solver is making.

3. When there isn't an available BCP deduction the solver uses DLIS 
(dynamic largest individual sum) heuristic for deciding which literal to
assign to True next. This heuristic provides a good rule of thumb which
experiments showed to shorten the search path dramatically. There are other
heuristics that are known to perform better than DLIS (such as VSIDS, EVSIDS,
VMTF) but they are currently not implemented in this repository.


## Theories
The repository provides a basic theory that serves as an interface for all
theories to be developed and 2 non-trivial theories - TQ theory and UF theory.
### TQ Theory
The theory of linear arithmetic over rational numbers. The TQ theory supports
basic logic operations and linear equations in the form of
ax = b / ax < b (and the negated operations !=, >=) where a is a vector
of numbers and b is a number.

### UF Theory  
The Theory of Uninterpreted Functions. The UF Theory supports basic logical
operations, functions (with single/multiple arity), and =, != operations.

The UF theory extends FOL (first-order logic) with = interpreted by 4 axioms:
1. Reflexivity
2. Symmetry
3. Transitivity
4. Congruence

The implementation of this theory is using a congruence graph it builds from the
assigned equalities. This graph is then examined in front of the assigned
inequalities.

## How To Use?
The solvers are easy to use and are accessible through two main objects:
A DPLL solver which only runs the SAT solver and a DPLLT which combines the SAT
solver with a theory of your choice. Here there will be a few examples of usage
for more you can check the different scenarios used in the tests.

1. **DPLL Solver** - An object which manages the run of SAT solver. The object
provides an option to give the solver an input formula that is already in
an abstracted form (list of sets of ints) and to solve for it directly. The
lack of theory solver in the DPLL makes the identity of the literals themselves
irrelevant and this format is conveniently close to the input formats of popular
SAT solvers (MiniSat, Glucose, etc.).

```python
from parsing.parse import Parser
from DPLLT import DPLL

parser = Parser()
solver = DPLL()

# With non-abstracted formula
formula_text = "(x -> y) | (!x)"
formula = parser.parse(formula_text)
solver.solve(formula)

# With abstracted formula
formula = [{-1, -4, 5}, {-4, 6}, {-5, -6, 7}, {-7, 8},{-2, -7, 9}, {-8, -9}, {-8, 9}]
solver.solve(formula, to_abstract=False)

```

2. **DPLLT Solver** - The full DPLLT solver solves the given formula with respect
to the given theory solver.


```python
from parsing.parse import Parser
from solvers.theories.UFTheory import UFTheory
from DPLLT import DPLLT

parser = Parser()
uf_theory = UFTheory()
solver = DPLLT(uf_theory)

formula_text = "(g(a) = c) & (((f(g(a)) != f(c)) | (g(a) = d)) & (c != d))"
formula = parser.parse(formula_text)
solver.solve(formula)

```
