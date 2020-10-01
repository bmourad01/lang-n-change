# lang-n-change

## What is it?

lang-n-change is a tool for transforming languages. It provides a DSL, L-Tr (pronounced "Elter"), for expressing algorithms that perform language transformations.

Given a language definition (`.lan` file) and an algorithm (`.tr` file), the algorithm is applied to the language definition, producing a new language definition.

L-Tr is based on a calculus described in [1]. A prototype of lang-n-change is presented in [2]. The current tool is a newer and vastly improved version of the prototype.

Algorithms expressed in L-Tr are compiled to an OCaml program which is then run with the language definition as the sole argument.

## Requirements

- OCaml (>= 4.08)
- a POSIX-compliant shell

Additionally, the following OCaml packages are required (available through `opam` via `opam install <pkg>`):

  "dune" {>= "2.7.1"}
  "core_kernel" {>= "0.14.0"}
  "menhir"
  "ppx_compare"
  "ppx_hash"
  "ppx_let"
  "ppx_sexp_conv"

- dune (>= 2.7.1)
- core_kernel (>= 0.14.0)
- ppx_compare
- ppx_hash
- ppx_let
- ppx_sexp_conv
- menhir

For compiling to λ-Prolog, the most recent version of Teyjus (https://github.com/teyjus/teyjus) is needed to execute the generated `.mod` and `.sig` files.

## Building

Run `dune build lnc` to build the project.

**DO NOT** run `dune build`, as the program `support/bin/transformer.ml` requires the generated `transform.ml` file, which is obviously not there by default.

## Transforming languages

Run `./transform <.lan> <.tr>`. The transformed language definition is printed to `stdout`.

## Compiling to Lambda-Prolog

Run `./lprolog <.lan>`. The generated `.mod` and `.sig` files are created in the directory `lp/<name of .lan>/` and compiled/linked using Teyjust (`tjcc` and `tjlink`, respectively).

## References

[1] Mourad B., Cimini M. (2020) A Calculus for Language Transformations. In: Chatzigeorgiou A. et al. (eds) SOFSEM 2020: Theory and Practice of Computer Science. SOFSEM 2020. Lecture Notes in Computer Science, vol 12011. Springer, Cham. https://doi.org/10.1007/978-3-030-38919-2_44
[2] Mourad B., Cimini M. (2020) System Description: Lang-n-Change - A Tool for Transforming Languages. In: Nakano K., Sagonas K. (eds) Functional and Logic Programming. FLOPS 2020. Lecture Notes in Computer Science, vol 12073. Springer, Cham. https://doi.org/10.1007/978-3-030-59025-3_12
