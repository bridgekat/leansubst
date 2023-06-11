# Leansubst

> This is still in very early stage and is definitely not as feature-complete as [Autosubst](https://github.com/coq-community/autosubst/). Rough implementation details can be seen everywhere. Renamings are not specially handled. Normalisation involving `shift`s and `up`s can get halfway stuck.

## How to use

See [`Examples.lean`](Leansubst/Examples.lean) (this will be simplified soon...)

For definitions and explanations, see [`Defs.lean`](Leansubst/Defs.lean) and [`Basic.lean`](Leansubst/Basic.lean).

There is plan to formalise the completeness and decidability proofs[^1] of the equational theory.

[^1]: [Completeness and Decidability of de Bruijn Substitution Algebra in Coq](https://www.ps.uni-saarland.de/Publications/documents/SchaeferEtAl_2015_Completeness.pdf) doi: [10.1145/2676724.2693163](https://doi.org/10.1145/2676724.2693163)
