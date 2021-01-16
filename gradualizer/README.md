# Gradualizer

As explained in the main [README](../README.md), this directory contains an implementation of the Gradualizers of Cimini and Siek, with the following algorithms implemented in *L-Tr*:

- `gradual_static.tr` generates the static semantics.
- `gradual_static_extended.tr` extends the previous algorithm to accomodate languages with subtyping and multiple contravariant types.
- `gradual_dynamic.tr` generates the dynamic semantics.

This directory has the following structure:

```
|-- dynamic
|   |-- *.lan (languages from the repo of https://github.com/mcimini/GradualizerDynamicSemantics)
|   `-- gradualized
|       `-- *.lan (the same languages, applied to gradual_dynamic.tr)
|-- static
|   |-- *.lan (languages from the repo of https://github.com/mcimini/Gradualizer)
|   `-- gradualized
|       `-- *.lan (the same languages, applied to gradual_static.tr)
|-- extra
|   |-- *.lan (languages not found in either repo)
|   |-- multiple_contra
|   |   `-- stlc_multiple_contra_*.lan (languages where multiple contravariant types are present)
|   |-- subtyping
|   |   `-- *_subtyping.lan (languages with subtyping applied, excludes those found in multiple_contra/)
|   `-- gradualized
|       |-- dynamic
|       |   `-- *.lan (the languages found in the base of extra/, applied to gradual_dynamic.tr)
|       `-- static
|           `-- *.lan (all the languages in extra/, applied to gradual_static.tr or gradual_static_extended.tr, where appropriate)
```
The languages in `extra/subtyping` were generated using an [existing algorithm](../examples/subtyping.tr) for adding subtyping.
Note that it does not handle languages with multiple contravariant types.
