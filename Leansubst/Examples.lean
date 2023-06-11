import Leansubst.Basic

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
This can be much more involved... Currently I don't know how to automate this.
-/

theorem to_expr_shift (s : Term) (n m : Nat) :
    toExpr (shift s n m) = Subst.apply (Subst.up n (Subst.shift _ m)) (toExpr s) := by
  induction s generalizing n with
  | var i =>
    rw [shift]
    split <;> simp only [toExpr, Subst.apply, Subst.apply.nested]
    case inl h =>
      have ⟨d, hd⟩ := Nat.le.dest h; subst hd; clear h
      congr; simp only [Subst.shift, Subst.up_get_high, Subst.applyr_def, Subst.apply, Function.comp]
      rw [Nat.add_comm n d, Nat.add_assoc, Nat.add_comm n m, Nat.add_assoc]
    case inr h =>
      congr; simp only [Subst.shift, Subst.up_get_low _ _ _ (Nat.lt_of_not_le h)]
  | app l r ihl ihr =>
    simp only [toExpr, Subst.apply, Subst.apply.nested]
    congr; exacts [ihl _, ihr _]
  | lam x r ih =>
    simp only [toExpr, Subst.apply, Subst.apply.nested]
    congr; exacts [ih _]

theorem to_expr_subst (s t : Term) (n : Nat) :
    toExpr (subst s n t) = Subst.apply (Subst.single n (toExpr t)) (toExpr s) := by
  induction s generalizing n with
  | var i =>
    rw [subst]
    split <;> (try split) <;> simp only [subst, toExpr, Subst.single, Subst.apply, Subst.apply.nested]
    case inl h =>
      congr
      cases i with
      | zero => contradiction
      | succ i =>
        have ⟨d, hd⟩ := Nat.le.dest (Nat.le_of_lt_succ h); subst hd; clear h
        rw [← Nat.add_succ, Subst.up_get_high, Subst.var_expand, Subst.applyr_def]
        rw [Nat.add_succ, Nat.pred_succ, Subst.cons]; simp only
        rw [Subst.id, Subst.apply, Function.comp, Subst.var_expand, Nat.add_comm]
    case inr.inl h₁ h₂ =>
      subst h₂; clear h₁
      conv => rhs; rhs; rw [← Nat.add_zero n]
      rw [Subst.up_get_high, to_expr_shift, Subst.up]; simp; rfl
    case inr.inr h₁ h₂ =>
      have h := Nat.lt_of_le_of_ne (Nat.le_of_not_lt h₁) (Ne.symm h₂); clear h₁ h₂
      rw [Subst.up_get_low _ _ _ h]
  | app l r ihl ihr =>
    simp only [subst, toExpr, Subst.single, Subst.apply, Subst.apply.nested]
    congr; exacts [ihl _, ihr _]
  | lam x r ih =>
    simp only [subst, toExpr, Subst.single, Subst.apply, Subst.apply.nested]
    congr; exacts [ih _]

/-!
Now we are finally ready to go!
-/

local notation t " ⟦" n:80 " ↟ " m:79 "⟧"  => shift t n m
local notation t " ⟦" n:80 " ↦ " t':79 "⟧" => subst t n t'

/-- Make it look better... -/
syntax "leansubst" : tactic
syntax "tidysubst" : tactic

macro_rules
  -- This expands everything to normal form.
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
  apply to_expr_inj
  leansubst

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
