# lang-n-change

## What is it?

*lang-n-change* is a tool for transforming languages.
It provides a domain-specific language, *L-Tr* (pronounced "Elter"), for expressing algorithms that perform language transformations.

Given a language definition expressed in the style of operational semantics (`.lan` file) and an algorithm (`.tr` file), the algorithm is applied to the language definition, producing a new language definition.
Algorithms expressed in *L-Tr* are compiled to an OCaml program (`support/transform.ml`) which is then run with the language definition as the sole argument.

## Why use it?

*L-Tr* allows language transformations to be expressed in a concise, declarative style, and in a way that resembles pen-and-paper notation.
It provides first-class datatypes representing components of language definitions, which can be passed around and manipulated at a fine-grained level.
Thus, it can save language designers considerable time and effort for automatically adding features to entire classes of languages.
On average, *L-Tr* algorithms are roughly 1/3 the size of the (rather idiomatic) generated OCaml code for said algorithms.

Additionally, language definitions can be compiled to executable λProlog logic programs.
This feature can be used to run queries on the generated languages in order to test their behavior.
Another useful feature of λProlog is that it is a statically-typed language.
Language definitions that are ill-formed will fail to compile to λProlog programs, allowing for users to identify certain classes of errors in their language designs/transformations.

## Any publications?

*L-Tr* is based on a calculus of the same name, described in [1].
A prototype of *lang-n-change* is presented in [2].
The current tool is a new and improved version of the prototype.

## Requirements

- OCaml (>= 4.08)
- a POSIX-compliant shell

Additionally, the following OCaml packages are required (available through `opam` via `opam install <pkg>`):

- core_kernel (>= 0.14.0)
- dune (>= 2.7.1)
- menhir
- ocamlformat
- ppx_compare
- ppx_hash
- ppx_let
- ppx_sexp_conv

For compiling to λProlog, the most recent version of Teyjus (https://github.com/teyjus/teyjus) is needed to compile and query the generated `.mod` and `.sig` files.
Teyjus is known to build with OCaml 4.08.1.
If you are using a newer version of the OCaml compiler, then it is recommended that you create a new switch on opam for building Teyjus: `opam switch create <name> 4.08.1`.

## How to build

Run `dune build lnc` to build the project.

**DO NOT** run `dune build`, as the program `support/transformer.ml` requires the generated `support/transform.ml` file, which is obviously not there by default.

## Transforming languages

Run `./transform <.tr> <.lan>`. The transformed language definition is printed to `stdout`.

### Examples

The following algorithms are found in the `examples/` directory:

- `big.tr` transforms a functional language to use big-step semantics.
- `pattern_matching.tr` adds pattern-matching as a top-level operator to a functional language. 
- `ref.tr` adds mutable references and other imperative-style features to a functional language.
- `subtyping.tr` adds algorithmic subtyping for a functional language (excludes width/row-subtyping).

Each of these algorithms assume that the input language uses small-step semantics with evaluation contexts.

Some sample language definitions are provided in the `lan/` directory:

- `fpl.lan` is a functional programming language combining features of the call-by-value Simply-Typed λ-Calculus (STLC) with lists, pairs, natural numbers, booleans, and so on, as well as universal types (a-la System F) and iso-recursive types.
- `mj.lan` is a simplified version of the MJ (Middleweight Java) calculus, as seen in [5].

### Gradualizer

The `gradualizer/` directory contains algorithms for adding gradual typing to a functional language. It is based on the methodologies described in [3] and [4], and contains one-to-one translations of the language repositories for both papers (`gradualizer/static/` and `gradualizer/dynamic/`, respectively; see https://github.com/mcimini/Gradualizer and https://github.com/mcimini/GradualizerDynamicSemantics).

Additionally, the directory `gradualizer/extra` contains languages not included in the repo of the original Gradualizer, including `stlc_multiple_contra.lan`
Furthermore, `gradualizer/extra/subtyping` contains the languages of our repo extended with subtyping using the algorithm found in `examples/subtyping.tr`.
Note that this algorithm does not cover languages with multiple consumers.

- `gradual_static.tr` generates the static semantics (type system), including the Cast Calculus.
- `gradual_static_extended.tr` extends the previous algorithm to accomodate languages with subtyping and multiple comsumers.
- `gradual_dynamic.tr` generates the dynamic semantics with elimination forms for the `cast` operator.

## Compiling to λProlog

Run `./lprolog <.lan>`.
The generated `.mod` and `.sig` files are created in the directory `lp/<name of .lan>/` and compiled/linked using Teyjus (`tjcc` and `tjlink`, respectively; note that these are assumed to be visible from your `PATH` environment variable).
To run queries/execute programs, first enter the aforementioned directory, and then run `tjsim <name of .lan> -s <query>`.

## TODO

- Add documentation for language definitions.
- Add documentation for *L-Tr*.
- Add more syntactic sugar to *L-Tr* to provide a more concise, declarative style that doesn't resemble a typical functional language.
- Separate the type-checker for *L-Tr* from the actual code generator, and produce a typed AST.
- Allow second-order (polymorphic) functions to be declared in *L-Tr*.
- Improve type inference for the *L-Tr* compiler. Currently it exists in a very limited form (i.e. it does not operate over the entire program), and it may diverge on certain inputs.
- Improve the error messages generated by the *L-Tr* compiler (line/column numbers would be a good start).
- Improve the λProlog backend (especially w.r.t. type inference).
- The parsers for language definitions and *L-Tr* (especially) have many grammar ambiguities to be resolved.
- Currently, formulae with a sugared syntax (i.e. `Gamma |- e : T` and `e --> e`) are hard-coded in the parsers. Users should be able to define these notations themselves without editing the parsers.

## References

[1] Mourad B., Cimini M. (2020) A Calculus for Language Transformations. In: Chatzigeorgiou A. et al. (eds) SOFSEM 2020: Theory and Practice of Computer Science. SOFSEM 2020. Lecture Notes in Computer Science, vol 12011. Springer, Cham. https://doi.org/10.1007/978-3-030-38919-2_44

[2] Mourad B., Cimini M. (2020) System Description: Lang-n-Change - A Tool for Transforming Languages. In: Nakano K., Sagonas K. (eds) Functional and Logic Programming. FLOPS 2020. Lecture Notes in Computer Science, vol 12073. Springer, Cham. https://doi.org/10.1007/978-3-030-59025-3_12

[3] Matteo Cimini and Jeremy G. Siek. 2016. The gradualizer: a methodology and algorithm for generating gradual type systems. In Proceedings of the 43rd Annual ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL '16). Association for Computing Machinery, New York, NY, USA, 443–455. DOI:https://doi.org/10.1145/2837614.2837632
 
[4] Matteo Cimini and Jeremy G. Siek. 2017. Automatically generating the dynamic semantics of gradually typed languages. In Proceedings of the 44th ACM SIGPLAN Symposium on Principles of Programming Languages (POPL 2017). Association for Computing Machinery, New York, NY, USA, 789–803. DOI:https://doi.org/10.1145/3009837.3009863 

[5] Bierman, G., Parkinson, M.J., & Pitts, A. (2003). MJ: An imperative core calculus for Java and Java with effects. https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-563.pdf
