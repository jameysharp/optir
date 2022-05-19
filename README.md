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
- The `get-N` unary operator to extract the Nth result from a tuple,
  numbered from 0
- The control flow operators, described below: `func`, `loop`, and
  `switch`, and nullary `get-N`

The input can also contain let-bindings, such as `(?x 21 (+ ?x ?x))`,
which is equivalent to `(+ 21 21)`. This is purely for convenience:
recursive definitions aren't allowed, so let-bindings are exactly
equivalent to writing out the bound expression everywhere the name is
used. Even without let-bindings, the dataflow graph is hash-consed so
repeated expressions get shared internally.

Control flow is based on the Regionalized Value State Dependence Graph
(RVSDG), as described in ["RVSDG: An Intermediate Representation for
Optimizing Compilers"][rvsdg-2020] and other papers. (["Perfect
Reconstructability of Control Flow from Demand Dependence
Graphs"][control-flow] is especially important as it shows that this
representation can be used for all control flow, including irreducible
control flow graphs.)

[rvsdg-2020]: https://arxiv.org/abs/1912.05036
[control-flow]: https://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.687.6305

## `func` and `call` operators

The `func-N-inputs-M-outputs` operator defines an anonymous function
which, when called, takes N inputs and produces M outputs. (It's called
"lambda" in the RVSDG papers.) Its operands are, in order:

- zero or more constant inputs, always appended to the N inputs from the
  caller,
- and M output expressions.

Within the output expressions, the inputs are available by means of the
`get-N` nullary operator. The constant inputs are intended primarily for
passing in the definitions of other functions. At the moment there's
nothing you can do with that which you couldn't do using let-bindings,
but once RVSDG "phi" nodes are implemented to allow mutually recursive
functions this should be useful.

The result of evaluating one of these operators is effectively the
"address" of the function. Using it requires passing this address and
any inputs to a separate `call` operator. (It's called "apply" in the
RVSDG papers.)

Here's a function which just returns the difference of its two
arguments, using a helper function to negate one of them:

```lisp
(?neg (func-1-inputs-1-outputs (* -1 get-0))
(func-2-inputs-1-outputs (+ get-0 (get-0 (call ?neg get-1))))
)
```

This is probably a good choice for inlining in pretty much any cost
model, and indeed, optir does so, producing this equivalent expression:

```lisp
(func-2-inputs-1-outputs (+ get-0 (* -1 get-1)))
```

Here's an example where I think optir's use of equality saturation on
e-graphs really shines:

```lisp
(?f (func-1-inputs-2-outputs (get-0 (loop get-0 (+ get-0 1) (+ get-0 -42))) 1)
(?call1 (call ?f 1)
(?call2 (call ?f 2)
(?call3 (call ?f 3)
(func-0-inputs-2-outputs
  (+ (get-0 ?call1) (+ (get-0 ?call2) (get-0 ?call3)))
  (+ (get-1 ?call1) (+ (get-1 ?call2) (get-1 ?call3)))
)))))
```

The e-graph for this program can represent both the inlined and
non-inlined variants at the same time. This allows rewriting based on
facts learned from inlining, even if extraction later decides that it's
worth keeping the function un-inlined. The implementation currently
produces this equivalent expression:

```lisp
(?f (func-1-inputs-2-outputs (get-0 (loop get-0 (+ get-0 1) (+ get-0 -42))) 1)
(func-0-inputs-2-outputs
  (+ (get-0 (call ?f 1)) (+ (get-0 (call ?f 2)) (get-0 (call ?f 3))))
  3))
```

The second output has been constant-folded to 3, even thought the first
output is still produced by calling `?f`.

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

Here's a complex example where the predicate is `get-0`, and there are
four inputs and four outputs. I've grouped the inputs and each case on
separate lines.

```lisp
(?nested (switch-2-cases-1-outputs 0 get-1 get-3 get-0 get-1)
(?outer (switch-2-cases-4-outputs
  get-0
  get-1 get-2 get-2 get-3
  get-0 get-0 get-1 (get-0 ?nested)
  get-0 get-1 get-2 get-1)
(func-4-inputs-4-outputs (get-0 ?outer) (get-1 ?outer) (get-2 ?outer) (get-3 ?outer))
))
```

This example can be simplified quite a bit without changing the
function's outputs. For example,

- output 0 is always equal to switch input 0 (which is `get-1`, or the
  second argument of the function) regardless of which case is
  evaluated;
- switch inputs 1 and 2 are equivalent, so within the switch outputs,
  any use of `get-2` can be replaced with `get-1`;
- the inner `switch` has a constant predicate so it can be replaced with
  the outputs of its case 0;
- after the inner `switch` is simplified, the outer switch's input 3 is
  never used, so it can be removed.

As of this writing, `cargo run --bin optir` applies all the above
simplifications and a few other similar cases to reduce that example to
this equivalent expression:

```lisp
(func-4-inputs-4-outputs
get-1
(get-0 (switch-2-cases-1-outputs get-0 get-1 get-2 get-0 get-1))
get-2
get-2)
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

Here's an expression to compute the nth natural power of x, if x and n
are provided as inputs 0 and 1, respectively:

```lisp
(func-2-inputs-1-outputs
(get-2
  (loop
  get-0 get-1 1
  (* get-0 get-0)
  (>> get-1 1)
  (get-0 (switch-2-cases-1-outputs (& get-1 1) get-0 get-2 get-1 (* get-1 get-0)))
  get-1)
))
```

Currently, optir does several loop optimizations, but I haven't really
tested them.

- If the loop's predicate is always false on the first iteration, then
  the loop body always runs exactly once and we can inline it into the
  surrounding code.

- If we can prove inductively that some pair of loop variables `x` and
  `y` have equivalent values at the boundaries of every loop iteration,
  then we can replace every use of `y` with `x`, both inside and after
  the loop. This generalizes to larger groups of variables.

- Loop-Invariant Code Motion: any expression in the loop body which
  depends only on loop-invariant variables can be hoisted out of the
  loop as a new loop-invariant input.

- Any uses of loop-invariant variables after the loop are replaced by
  the corresponding loop inputs, which can expose more opportunities to
  apply algebraic identities. Then, loop-invariant variables which are
  not used in the body of the loop are removed from the loop.

I think these optimizations are all easier on the RVSDG than they would
be on a control-flow graph. Together they're implemented in under 300
lines of Rust, and rely only on a couple of very simple bottom-up
dataflow analyses. The underlying graph implementation supports cheap
checks for whether two expressions are equivalent, modulo a given set of
rewrite rules, which helps a lot.

Loop peeling looks easy to do in this framework too, but I haven't tried
implementing it yet.

# CFG input language

I've also implemented conversion from control-flow graphs to RVSDGs,
following the algorithm in ["Perfect Reconstructability of Control Flow
from Demand Dependence Graphs"][control-flow], section 4. Input is in a
kind of assembly language in the style of three-address code. Its
primary feature is that it was easy for me to parse.

Each instruction, label, and function definition gets its own line.
Comments are introduced with either `#` or `;` and extend to the end of
the line. Tokens are separated by whitespace but whitespace is not
otherwise significant. Variable and label identifiers can be any
sequence of non-whitespace Unicode characters unless they're either a
signed integer or the special token `->`.

A CFG begins with a function definition of the form `function ->`
followed by the names of any arguments to the function. (The `->` can be
omitted if there are no arguments.)

A block of instructions can be labeled with `label` followed by an
identifier, and branched to with `goto` followed by an identifier. If a
block ends without a branch instruction, it implicitly falls through to
the next block.

Conditional branches are defined with `switch`, followed by a variable
name, and then two or more label names. The value of the variable must
be between 0 and the number of labels, minus one, and selects which
label to branch to.

The function's result is determined by a `return` statement, followed by
a sequence of variable names (or constants) to return.

Statements are either `mov x -> y` meaning to copy the value in `x` into
`y`, or are an operator from the RVSDG language above. The operator name
(`*`, `>>`, etc) goes first, then its operands, then the `->` token, and
then the names to assign its results to.

Here's a CFG to compute the nth natural power of x, corresponding to the
example above for RVSDG loops:

```
function -> x n
  mov 1 -> y
label loop
  & n 1 -> c
  switch c even odd
label odd
  * y x -> y
label even
  * x x -> x
  = n 0 -> c
  >> n 1 -> n
  switch c done loop
label done
  return y
```

Note that if nothing is returned, then none of the computation in the
function is needed and the generated RVSDG will be empty! For
non-terminating and side-effecting functions, you need an extra `state`
parameter to the function, which you need to thread through every
operation that must execute, and then finally return the state as part
of the function's result.

In addition, if you don't have any side-effecting operations in the body
of a loop and want to preserve non-termination, add a `use state ->
state` statement. At runtime it's a no-op, but it keeps the state
variable from appearing to be loop-invariant.

Even irreducible control flow is allowed, but there are currently two
constraints on control flow. First, there must be exactly one return
statement in the function, though it can appear anywhere. Second,
infinite loops must have a branch that can reach the return statement,
even if that branch can never be taken dynamically.

Illustrating these requirements, here's an example of a function which
decides whether to return or to loop forever based on its argument. The
`switch 1` statement always branches to its second label, but the first
label is still there to signal to the transformation how to thread the
state variable through the generated RVSDG.

```
function -> state should-halt
  switch should-halt forever done
label forever
  use state -> state
  switch 1 done forever
label done
  return state
```

Running `cargo run --bin build-rvsdg` on that example generates this
RVSDG:

```lisp
(func-2-inputs-1-outputs
  (get-0
    (switch-2-cases-1-outputs get-1 get-0 (get-0 (loop get-0 (use get-0) 1)) get-0)))
```

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
involving variadic operators like `loop`, `switch`, and `func`. But it
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
