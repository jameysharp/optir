# optir: "optimizing intermediate representation"

This is a proof-of-concept of applying optimizations in a compiler using
e-graphs and the Regionalized Value State Dependence Graph. It is not
useful as-is. It's a toy to illustrate how these two research areas can
be applied together, and to explore some implementation details without
needing to work in the context of a real compiler.

# RVSDG input language

The input language uses s-expressions to describe a tree of operators.
There are several kinds of operators:

- Constant numbers, such as `-42`
- Binary operators, such as `(+ 5 (* -1 2))`
- The `copy` operator, whose result is a tuple of its operands
- The `get-N` unary operator to extract the Nth result from a tuple:
  `(get-1 (copy 1 2 3))` is equivalent to `2`
- The control flow operators `loop` and `switch` and nullary `get-N`,
  described below

Control flow is based on the Regionalized Value State Dependence Graph
(RVSDG), as described in ["RVSDG: An Intermediate Representation for
Optimizing Compilers"][rvsdg-2020] and other papers. (["Perfect
Reconstructability of Control Flow from Demand Dependence
Graphs"][control-flow] is especially important as it shows that this
representation can be used for all control flow, including irreducible
control flow graphs.)

[rvsdg-2020]: https://arxiv.org/abs/1912.05036
[control-flow]: https://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.687.6305

## `switch` operator

The `switch-N-cases-M-outputs` operator is a generalized form of
"if-then-else". (It's called "gamma" in the RVSDG papers.) Its operands
are, in order:

- a predicate whose value must range from 0 to N-1,
- zero or more inputs,
- and M outputs for each of the N cases.

The predicate's value at runtime selects which case should be evaluated.
The result of the `switch` expression is then a tuple of the M outputs
of that case. Within the expression for an output, you can use the
nullary `get-N` operator to refer to the Nth input to the enclosing
`switch`.

Here's a complex example where the predicate is `get-9`, and there are
four inputs and four outputs. I've grouped the inputs and each case on
separate lines.

```lisp
(switch-2-cases-4-outputs
get-9
get-5 get-6 get-6 get-7
get-0 get-0 get-1 (get-0 (switch-2-cases-1-outputs 0 get-1 get-3 get-0 get-1))
get-0 get-1 get-2 get-1)
```

This example can be simplified quite a bit without changing its outputs.
For example,

- output 0 is always equal to input 0 (which is `get-5`) regardless of
  which case is evaluated;
- input 1 is equal to input 2, so within the outputs, any use of `get-2`
  can be replaced with `get-1`;
- the inner `switch` has a constant predicate so it can be replaced with
  the outputs of its case 0;
- after the inner `switch` is simplified, the outer switch's input 3 is
  never used, so it can be removed.

As of this writing, optir applies all the above simplifications and a
few other similar cases to reduce that example to this equivalent
expression:

```lisp
(copy
get-5
(get-0 (switch-2-cases-1-outputs get-9 get-5 get-6 get-0 get-1))
get-6
get-6)
```

## `loop` operator

The `loop` operator represents a tail-controlled loop. (It's called
"theta" in the RVSDG papers.) Like a `do`/`while` loop in C-like
languages, this loop always runs once before evaluating a predicate to
determine whether to run another iteration. Its operands are, in order:

- N initial loop inputs,
- N loop body results,
- and a predicate whose value must be 0 or 1.

Unlike `switch`, N can be inferred from the total number of operands and
isn't explicitly specified.

For the first iteration of the loop, the arguments to the loop body come
from the loop's inputs. The loop body's results and the predicate are
evaluated using those arguments. Then, if the predicate is 0, the loop
ends; the body's results become the output of the loop. Otherwise, a new
iteration begins, with the body's arguments coming from the results of
the previous iteration.

Inside the expression for a result or predicate, nullary `get-N` refers
to the Nth argument to the loop body in the current iteration.

Currently, optir doesn't do any loop optimizations, so I haven't really
tested this operator.

# e-graphs good

Tree rewriting optimizations are implemented using the [egg][]
implementation of e-graphs for Rust. A vertex in this graph represents
not just one operator, but the equivalence class of every operator which
computes the same output.

[egg]: https://egraphs-good.github.io/

The `egg` library makes it easy to express algebraic identities. For
example:

- commutativity: `(+ ?x ?y)` &rArr; `(+ ?y ?x)`
- factoring: `(+ (* ?a ?b) (* ?a ?c))` &rArr; `(* ?a (+ ?b ?c))`
- bit hacks: `(% ?a ?c)` &rArr; `(& ?a (+ ?c -1))` if `is_power_of_two("?c")`

It does not provide any simple syntax like that to express rewrite rules
involving variadic operators like `loop`, `switch`, and `copy`. But it
does provide a hook for running arbitrary passes over the e-graph
periodically during equality saturation, which let me implement those
rewrites as (rather more verbose) Rust.

I implemented constant-folding by roughly following the examples in the
`egg` source tree. I've also implemented an analysis to track which
`loop`/`switch` arguments are possibly used by each e-class; this helps
guide the `switch` rewrite rules.

# Conclusions

This experiment has been fun and worked out quite well. I definitely
think people working on compilers should be aware of the potential of
these techniques. I hope this research prototype serves as some evidence
of how e-graphs and RVSDGs can play together.