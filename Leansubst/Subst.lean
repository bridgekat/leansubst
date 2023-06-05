import Mathlib.Tactic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

namespace Subst

-- The following definitions generalise over signatures (type of syntax tree nodes).
variable (σ : Type)

/-- Abstract syntax tree using de Bruijn indices. -/
inductive Expr where
  | var    : Nat →           Expr -- De Bruijn index.
  | binder : Expr →          Expr -- Marker for binder presence.
  | node   : σ → List Expr → Expr -- Tree node.
-- Nested inductive types (e.g. the `List Expr` here) are a special case of mutual inductive types.

mutual
/-- Simultaneous substitions are known to greatly simplify proofs (or do they...?)
    See: https://www.ps.uni-saarland.de/Publications/documents/SchaeferEtAl_2015_Autosubst_-Reasoning.pdf -/
inductive Subst where
  | id    :                 Subst
  | shift :                 Subst
  | cons  : ES → Subst →    Subst
  | then  : Subst → Subst → Subst

/-- Explicit substitutions are required since termination of rewriting is nontrivial. -/
inductive ES where
  | subst  : ES → Subst →  ES -- Substitution.
  | var    : Nat →         ES
  | binder : ES →          ES
  | node   : σ → List ES → ES
end

/-- Deterministic small-step rewriting rules. Returns strictly reduced `ES` or normal form `Expr`.
    See: https://www.hpl.hp.com/techreports/Compaq-DEC/SRC-RR-54.pdf (page 11) -/
def rewrite : ES σ → ES σ ⊕ Expr σ
  | .subst (.subst e s)   t                     => .inl $ .subst e (.then s t)
  | .subst (.var i)       .id                   => .inl $ .var i
  | .subst (.var i)       .shift                => .inl $ .var (.succ i)
  | .subst (.var 0)       (.cons e _)           => .inl $ e
  | .subst (.var (i + 1)) (.cons _ s)           => .inl $ .subst (.var i) s
  | .subst (.var i)       (.then .id s)         => .inl $ .subst (.var i) s
  | .subst (.var i)       (.then .shift s)      => .inl $ .subst (.var (i + 1)) s
  | .subst (.var i)       (.then (.cons h s) t) => .inl $ .subst (.var i) (.cons (.subst h t) (.then s t))
  | .subst (.var i)       (.then (.then s t) u) => .inl $ .subst (.var i) (.then s (.then t u))
  | .subst (.binder e)    s                     => .inl $ .binder (.subst e (.cons (.var 0) (.then s .shift)))
  | .subst (.node n es)   s                     => .inl $ .node n (es.map $ fun e => .subst e s)
  | .var i     => .inr $ .var i
  | .binder e  =>
    match rewrite e with
      | .inl e' => .inl $ .binder e'
      | .inr e' => .inr $ .binder e'
  | .node n es =>
    match rewrites es with
      | .inl es' => .inl $ .node n es'
      | .inr es' => .inr $ .node n es'
where
  rewrites : List (ES σ) → List (ES σ) ⊕ List (Expr σ)
    | []       => .inr []
    | e :: es  =>
      match rewrite e with
        | .inl e' => .inl $ e' :: es
        | .inr e' =>
          match rewrites es with
            | .inl es' => .inl $ e :: es'
            | .inr es' => .inr $ e' :: es'
termination_by
  rewrite e   => sizeOf e
  rewrites es => sizeOf es

/-
/-- Small-step reduction reduces measure. -/
theorem rewrite_normalises : ∀ (es : ES),
    (∃ n, rewrite es = .norm n) ∨
    size (rewrite es) < size es := by
  intros es
  induction es <;> (try left; eq_refl) <;> dsimp only [rewrite, ES.size, Subst.size]
  case sub e s ih₁ =>
    -- rcases ih₁ with ⟨n, ih₁⟩ | ih₁
    induction e <;> dsimp only [rewrite, ES.size, Subst.size]
    case sub e t ih₂ =>
      sorry

/-- Multi-step reduction. -/
def ES.apply : ES → ES :=
  fun 

/-- Apply simultaneous substitution. -/
def Expr.apply : Expr → Subst → Expr :=
  fun 

/-- Apply simultaneous substitution. -/
def Expr.apply : Expr → Subst → Expr
  | .sort s,      _         => .sort s
  | .var i,       .id       => .var i
  | .var i,       .shift    => .var (.succ v)
  | .var 0,       .cons e _ => e
  | .var (v + 1), .cons e t => Expr.apply (.var i) t
  | .var i,       .then s t => Expr.apply (Expr.apply (.var i) s) t
  | .app l r,     s         => .app (Expr.apply l s) (Expr.apply r s)
  | .lam t e,     s         => .lam (Expr.apply t s) (Expr.apply e (.cons (.var 0) (.then s .shift)))
  | .pi t₁ t₂,    s         => .pi (Expr.apply t₁ s) (Expr.apply t₂ (.cons (.var 0) (.then s .shift)))
termination_by
  Expr.apply e s => aux e s

scoped notation "↟"             => Subst.shift
scoped notation e:80 " ⬝ " f:79 => Subst.cons e f

scoped notation e " ⟦" n:80 " ↦ " e':79 "⟧" => Subst.subst e n e'
scoped notation e " ⟦" n:80 " ↟ " m:79 "⟧"  => Subst.shift e n m
-/

end Subst
