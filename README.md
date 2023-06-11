# Leansubst

Leansubst is a library for the [Lean theorem prover](https://leanprover.github.io/) which provides basic automation for formalising syntactic theories with variable binders.

Given:

1. An **injective map** from arbitrary user-defined syntactic object type to `Leansubst.Expr`,
2. A proof that some user-defined substitution operation **agrees with** `Leansubst.Subst.apply`,

the `@[simp]` lemmas supplied by Leansubst will be able to automatically prove some simple facts about substitutions.

> ⚠ This is still in very early stage and is definitely not as feature-complete as [Autosubst](https://github.com/coq-community/autosubst/). Rough implementation details can be seen everywhere. Renamings are not specially handled. Normalisation involving `shift`s and `up`s can get halfway stuck.

## Installation

Add the following lines to the `lakefile.lean` file of your Lean 4 project:

```lean
require leansubst from git
  "https://github.com/bridgekat/leansubst" @ "main" -- Or replace "main" with a fixed commit hash
```

and run `lake update` in the same directory.

## How to use

- See [`Examples.lean`](Leansubst/Examples.lean) for using Leansubst on a simple λ-calculus with pointwise substitutions defined.
- For the definitions used by Leansubst, see [`Defs.lean`](Leansubst/Defs.lean) and [`Pointwise.lean`](Leansubst/Pointwise.lean).
- For theorems and explanations, see the comments in [`Basic.lean`](Leansubst/Basic.lean).

```lean
-- ... (User-supplied proof for `to_expr_inj`, `to_expr_shift` and `to_expr_subst`)

example (s) :
    .lam "x" (.app (.var 0) (.var 3)) ⟦2 ↦ s⟧ =
    .lam "x" (.app (.var 0) (s ⟦0 ↟ 3⟧)) := by
  apply to_expr_inj -- Start by turning the problem into one that Leansubst can recognise.
  leansubst         -- Normalise!
```

There is also some plan to formalise the completeness and decidability proofs[^1] of the equational theory.

## Bug reports

Please submit bugs reports on [https://github.com/bridgekat/leansubst/issues](https://github.com/bridgekat/leansubst/issues).

[^1]: [Completeness and Decidability of de Bruijn Substitution Algebra in Coq](https://www.ps.uni-saarland.de/Publications/documents/SchaeferEtAl_2015_Completeness.pdf) doi: [10.1145/2676724.2693163](https://doi.org/10.1145/2676724.2693163)
