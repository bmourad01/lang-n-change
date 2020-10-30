# lang-n-change

## What is it?

lang-n-change is a tool for transforming languages.
It provides a domain-specific language, L-Tr (pronounced "Elter"), for expressing algorithms that perform language transformations.

Given a language definition (`.lan` file) and an algorithm (`.tr` file), the algorithm is applied to the language definition, producing a new language definition.

L-Tr is based on a calculus described in [1].
A prototype of lang-n-change is presented in [2].
The current tool is a new and improved version of the prototype.

Algorithms expressed in L-Tr are compiled to an OCaml program (`support/transform.ml`) which is then run with the language definition as the sole argument.

Additionally, language definitions can be compiled to executable λProlog logic programs.
This feature can be used to run queries on the generated languages in order to test their behavior.

## Requirements

- OCaml (>= 4.08)
- a POSIX-compliant shell

Additionally, the following OCaml packages are required (available through `opam` via `opam install <pkg>`):

- core_kernel (>= 0.14.0)
- dune (>= 2.7.1)
- menhir
- ppx_compare
- ppx_hash
- ppx_let
- ppx_sexp_conv

For compiling to λProlog, the most recent version of Teyjus (https://github.com/teyjus/teyjus) is needed to execute the generated `.mod` and `.sig` files.

## Building

Run `dune build lnc` to build the project.

**DO NOT** run `dune build`, as the program `support/transformer.ml` requires the generated `support/transform.ml` file, which is obviously not there by default.

## Transforming languages

Run `./transform <.lan> <.tr>`. The transformed language definition is printed to `stdout`.

## Compiling to λProlog

Run `./lprolog <.lan>`. The generated `.mod` and `.sig` files are created in the directory `lp/<name of .lan>/` and compiled/linked using Teyjus (`tjcc` and `tjlink`, respectively).

## TODO

- Add documentation for language definitions.
- Add documentation for L-Tr.
- Separate the type-checker for L-Tr from the actual code generator, and produce a typed AST.
- Improve type inference for the L-Tr compiler. Currently it exists in a very limited form (i.e. it does not operate over the entire program).
- Improve the error messages generated by the L-Tr compiler (line/column numbers would be a good start).
- Improve the λProlog backend (especially w.r.t. type inference).

## References

[1] Mourad B., Cimini M. (2020) A Calculus for Language Transformations. In: Chatzigeorgiou A. et al. (eds) SOFSEM 2020: Theory and Practice of Computer Science. SOFSEM 2020. Lecture Notes in Computer Science, vol 12011. Springer, Cham. https://doi.org/10.1007/978-3-030-38919-2_44

[2] Mourad B., Cimini M. (2020) System Description: Lang-n-Change - A Tool for Transforming Languages. In: Nakano K., Sagonas K. (eds) Functional and Logic Programming. FLOPS 2020. Lecture Notes in Computer Science, vol 12073. Springer, Cham. https://doi.org/10.1007/978-3-030-59025-3_12
