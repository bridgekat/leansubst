import Leansubst.Basic
import Leansubst.Pointwise

/-- A simple lambda calculus with custom variable substitution operation. -/
inductive Term where
  | var : Nat →           Term -- Variable in de Bruijn index.
  | app : Term → Term →   Term -- Function application.
  | lam : String → Term → Term -- Function abstraction.

def shift : Term → Nat → Nat → Term
  | .var v,    n, m => if n <= v then .var (v + m) else .var v
  | .app l r,  n, m => .app (shift l n m) (shift r n m)
  | .lam x r,  n, m => .lam x (shift r (n + 1) m)

def subst : Term → Nat → Term → Term
  | .var v,    n, t => if n < v then .var (.pred v) else if n = v then shift t 0 n else .var v
  | .app l r,  n, t => .app (subst l n t) (subst r n t)
  | .lam x r,  n, t => .lam x (subst r (n + 1) t)

/-!
To use Leansubst v0.1, we need to map `Term` to `Leansubst.Expr`.
This requires us to provide a signature.

If your terms are defined in more than one mutually inductive types,
it suffices to map everything into one single type `Leansubst.Expr` (as long as it is an injection).
-/

inductive Sig where
  | var :          Sig
  | app :          Sig
  | lam : String → Sig

def toExpr : Term → Leansubst.Expr Sig
  | .var i   => .var i                              -- `var` must be mapped to `var` (no "fancy" variables).
  | .app l r => .node .app     [toExpr l, toExpr r] -- `app` is a node with two children.
  | .lam x r => .node (.lam x) [.binder (toExpr r)] -- `lam` is a node with one child "inside" a binder.

open Leansubst

abbrev Expr := Leansubst.Expr Sig
abbrev Subst := Leansubst.Subst Sig

/-!
Now we prove that the mapping is an injection.
This should be trivial (simply keep applying `injection`s).
-/

theorem to_expr_inj (s t : Term) : toExpr s = toExpr t → s = t := by
  induction s generalizing t with
  | var i =>
    cases t <;> intros <;> try injections
    rename_i h; rw [h]
  | app l r ihl ihr =>
    cases t <;> intros <;> try injections
    rename_i l' r' h; injection h with _ h; injections h₁ _ h₂ _
    congr; exacts [ihl _ h₁, ihr _ h₂]
  | lam x r ih =>
    cases t <;> intros <;> try injections
    rename_i x' r' h; injection h with _ h; injections h₁ _ _ h₂
    congr; exact ih _ h₂

/-!
And that our own substitution function agrees with `Leansubst.Subst.apply`.
This can be done by using results from `Leansubst.Pointwise` (and keep unfolding definitions).
-/

theorem to_expr_shift (t : Term) (n m : Nat) :
    toExpr (shift t n m) = Subst.apply (Subst.up n (Subst.shift Sig m)) (toExpr t) := by
  rw [← Pointwise.shift_to_parallel]
  induction t generalizing n with
  | var i =>
    simp only [toExpr, shift, Pointwise.shift]
    split <;> (try split) <;> trivial
  | app l r ihl ihr =>
    simp only [toExpr, shift, Pointwise.shift, ihl, ihr]
    simp only [Pointwise.shift, Pointwise.shift.nested]
  | lam x r ih =>
    simp only [toExpr, shift, Pointwise.shift, ih]
    simp only [Pointwise.shift, Pointwise.shift.nested]

theorem to_expr_subst (s t : Term) (n : Nat) :
    toExpr (subst s n t) = Subst.apply (Subst.pointwise n (toExpr t)) (toExpr s) := by
  rw [← Pointwise.subst_to_parallel]
  induction s generalizing n with
  | var i =>
    simp only [toExpr, subst, Pointwise.subst]
    split <;> (try split) <;> try trivial
    rw [to_expr_shift, Pointwise.shift_to_parallel]
  | app l r ihl ihr =>
    simp only [toExpr, subst, Pointwise.subst, ihl, ihr]
    simp only [Pointwise.subst, Pointwise.subst.nested]
  | lam x r ih =>
    simp only [toExpr, subst, Pointwise.subst, ih]
    simp only [Pointwise.subst, Pointwise.subst.nested]

/-!
Now we are finally ready to go!
-/

/-- Make it look better... -/
local notation t " ⟦" n:80 " ↟ " m:79 "⟧"  => shift t n m
local notation t " ⟦" n:80 " ↦ " t':79 "⟧" => subst t n t'

/-!
Currently, Leansubst does not implement any tactics.
You may start by copying the implementations below, and add your own enhancements later.
-/

syntax "leansubst" : tactic
syntax "tidysubst" : tactic

macro_rules

  -- This tries to expand everything to normal form.
  | `(tactic| leansubst) => `(tactic|
    simp only [toExpr, to_expr_shift, to_expr_subst];
    simp [Nat.add_zero, Nat.zero_add, Nat.add_succ, Nat.succ_add])

  -- This restores you some sanity (hopefully...) in case anything stucks.
  | `(tactic| tidysubst) => `(tactic|
    simp only [Subst.var0, Subst.shift1, Subst.shift_comp_shift, Subst.up_up];
    simp only [← Subst.var_expand, ← Subst.comp_assoc];
    simp only [← Subst.apply_apply];
    simp only [Subst.apply, Subst.id, Subst.shift, Subst.cons, Subst.up])

-- A working example.
example (s) :
    .lam "x" (.app (.var 0) (.var 3)) ⟦2 ↦ s⟧ =
    .lam "x" (.app (.var 0) (s ⟦0 ↟ 3⟧)) := by
  apply to_expr_inj -- Start by turning the problem into one that Leansubst can recognise.
  leansubst         -- Normalise!

-- A non-working example.
example (s n) :
    .lam "x" (.app (.var 0) (.var (n + 3))) ⟦(n + 2) ↦ s⟧ =
    .lam "x" (.app (.var 0) (s ⟦0 ↟ (n + 3)⟧)) := by
  apply to_expr_inj
  leansubst; tidysubst
  -- Stuck at `up n`; requires manual proof of inequality.
  rw [Nat.add_comm 0 n, Subst.up_get_high]
  leansubst; tidysubst
  -- Stuck; requires manual conversion of renaming functions to `shift`.
  have h : (fun i => Expr.var (0 + (1 + (1 + (1 + i))))) = Subst.shift Sig 3 :=
    funext $ fun i => by simp only [Nat.zero_add, Nat.one_add, Subst.shift]
  rw [h]; clear h
  have h : Expr.var ∘ (fun x => x + n) = Subst.shift Sig n := rfl
  rw [h]; clear h
  have h : (fun i => Expr.var (0 + (1 + (1 + (1 + (i + n)))))) = Subst.shift Sig (n + 3) :=
    funext $ fun i => by simp only [Nat.zero_add, Nat.one_add, Subst.shift, Nat.add_succ]
  rw [h]; clear h
  leansubst; tidysubst
  -- Stuck; requires manual proof of equality.
  congr
  apply funext; intros i; rw [Nat.add_comm n, Nat.add_assoc, Nat.add_assoc]
