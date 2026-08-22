# Props2Theories

## Common words about the repository:

This course covers the most important foundations, core knowledge, and applications of mathematics (sometimes with reference to Pure Math, and sometimes to Theoretical Computer Science).

The course structure in this repository closely resembles that of my Voltage2Services course.

The difference is that this is not about programming; it is about mathematics.

It explains the basics of math, starting from logic and set axioms and proceeding to fundamental abstractions in pure math and applications in theoretical computer science.

However, it goes much deeper and is at a higher level than many well-known courses.

Let's call this Props2Theories.

For this course, all fundamental mathematical objects and theorems about them (with full solution proofs) will be added, so the course will evolve over time.

It will be a long-term work in progress.

## Course structure

The course consists of different mathematical subjects.

Each subject is divided into multiple chapters, subchapters etc.

If a chapters is terminal, we called it topic.

- Your task is to prove the listed theorems for each topic in `Task.lean`.
- In each topic, you will also find solutions in `Solution.lean`.

The course is structured in such a way that you usually only need knowledge from previous tasks, along with your creativity and ability to carefully construct proofs.

## Technical instructions:

The required software to install includes Lean, Vs Code, Lake, Elan

1. Install `VS Code`.
2. Install the VS Code extension `lake`, `lean`, `elan`
3. Install `Lean 4` VS Code extension

Look up installation instructions online for your system.

4. The root directory contains `Props2Theories` subdirectory,
   we will work there

5. We will use my `TacticNames.lean` and `Axioms.lean` files

I generally expect you to use Linux, although it can usually also be installed on macOS and Windows. However, it is your responsibility to install VS Code and everythin needed for the project.

## About the choice of fundamentals

We will use:

1. `Natural Deduction` rules, defined as tactics in the `TacticNames.lean` file

- Rules for `Propositional Logic` (`Intuitionistic` + `Classical`)
- Rules for `Higher-Order Predicate Logic`
- Rules for `Equality`

2. `Set` Type, declared in the `Axioms.lean` file

3. `∈` (`Belongs`) Predicated

4. `℩` (the `iota operator`) and its properties for `Definite Descriptions`, declated in the `Axioms.lean` file

5. `Set Theory` axioms, declared in `Axioms.lean` file

All mathematics will be built upon these foundations.

We will not always need all rules and all axioms.

Depending on the rules and axioms, we choose among the all, we can work within seven different `Set Theory` systems!

I am aware that `CIC` (`Calculus of Inductive Constructions`) `Type Theory` as a mathematical foundation is more convenient in LEAN and includes many built-in primitives in the language or libraries.

Moreover, together with lambda calculus, it allows for much more convenient computable reductions of certain expressions (for example, in arithmetic).

Also, in Lean or in other proof assistants (such as `Coq`), there are advanced tactics that can simplify some trivial but tedious proofs.

We could even have chosen fancy `HoTT` (`Homotopy Type Theory`) as the foundational system.

You could also argue that the axiomatic structure of our `Set Theory` is not the most natural fit for Lean, which primarily follows constructive logic.

However, in this GitHub repository, I explicitly want you to experience the "hardcore" approach.

It is useful to understand how to build mathematical abstractions from abstract `Logic Rules` and `Set Theory Axioms` using non-trivial ideas.

Have fun! 😀

## P.S

If you really want to learn about topics such as:

- Basic functional programming fundamentals, including lambda calculus
- Type theories
- Proof assistants

and build your own compilers for different functional languages such as:

- Untyped
- Haskell-like
- Lean/Coq/Agda-like

you can study the `Functional` chapter of my other comprehensive Voltage2Services course, which teaches functional programming and type theory.
