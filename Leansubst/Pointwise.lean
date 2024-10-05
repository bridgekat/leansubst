import Leansubst.Basic

/-!
This file contains an alternative definition of variable substitution, and theorems
establishing their equivalence with the parallel substitution defined in `Defs.lean`.

If your definition of substitution more closely resembles the following,
it can be easier to prove the required lemmas based on the results below.
-/

namespace Leansubst.Pointwise

variable {σ : Type}

/-!
A [common definition](https://en.wikipedia.org/wiki/De_Bruijn_index#Formal_definition)
of pointwise substitutions.
-/

/-- Shift variables with level ≥ `n` by `m` levels. -/
def shift : Nat → Nat → Expr σ → Expr σ
  | n, m, .var i     => if n <= i then .var (i + m) else .var i
  | n, m, .binder e  => .binder (shift (n + 1) m e)
  | n, m, .node x es => .node x (nested n m es)
where nested : Nat → Nat → List (Expr σ) → List (Expr σ)
  | _, _, []      => []
  | n, m, e :: es => shift n m e :: nested n m es

/-- Replace all variables at level = `n` by an expression `t`,
    while decrementing all variables at level > `n`. -/
def subst : Nat → Expr σ → Expr σ → Expr σ
  | n, t, .var i     => if n < i then .var (.pred i) else if n = i then shift 0 n t else .var i
  | n, t, .binder e  => .binder (subst (n + 1) t e)
  | n, t, .node x es => .node x (nested n t es)
where nested : Nat → Expr σ → List (Expr σ) → List (Expr σ)
  | _, _, []      => []
  | n, t, e :: es => subst n t e :: nested n t es

/-- `Pointwise.shift n m` agrees with `Subst.apply (Subst.up n (Subst.shift m))`. -/
@[simp]
theorem shift_to_parallel (n m) : shift n m = Subst.apply (Subst.up n (Subst.shift σ m)) := by
  apply funext; intros e;
  -- Induction on `e`.
  let motive := fun (e : Expr σ) => ∀ n m, shift n m e = Subst.apply (Subst.up n (Subst.shift σ m)) e
  apply @Expr.recOn _ (fun e => motive e) (List.foldr (fun e etc => motive e ∧ etc) True)
    <;> intros <;> (try trivial) <;> intros n m
  case var i =>
    rw [shift, Subst.apply]
    split
    case isTrue h =>
      have ⟨d, hd⟩ := Nat.le.dest h; subst hd; clear h
      rw [Subst.up_get_high_applyr, Subst.shift, Subst.applyr]
      rw [Nat.add_assoc, Nat.add_comm, Nat.add_assoc]
    case isFalse h =>
      have h' := Nat.lt_of_not_le h; clear h
      rw [Subst.up_get_low]; exact h'
  case binder e ih => rw [shift, Subst.apply, Subst.up_up, ih]
  case node x es ih =>
    induction es with
    | nil => simp only [shift, shift.nested, Subst.apply, Subst.apply.nested]
    | cons h' t' ih' =>
      rw [List.foldr] at ih
      simp only [shift, shift.nested, Subst.apply, Subst.apply.nested] at *
      congr 2
      . exact ih.left _ _
      . specialize ih' ih.right
        injection ih'

/-- `Pointwise.subst n t` agrees with `Subst.apply (Subst.pointwise n t)`. -/
@[simp]
theorem subst_to_parallel (n t) : @subst σ n t = Subst.apply (Subst.pointwise n t) := by
  apply funext; intros e;
  -- Induction on `e`.
  let motive := fun (e : Expr σ) => ∀ n t, @subst σ n t e = Subst.apply (Subst.pointwise n t) e
  apply @Expr.recOn _ (fun e => motive e) (List.foldr (fun e etc => motive e ∧ etc) True)
    <;> intros <;> (try trivial) <;> intros n t
  case var i =>
    rw [subst, Subst.pointwise, Subst.id, Subst.apply]
    split <;> try split
    case isTrue h =>
      cases i with
      | zero => contradiction
      | succ i =>
        have h' := Nat.le_of_lt_succ h; clear h
        have ⟨d, hd⟩ := Nat.le.dest h'; subst hd; clear h'
        rw [Nat.pred_succ, Nat.add_one, ← Nat.add_succ]
        rw [Subst.up_get_high_applyr, Subst.cons, Subst.applyr, Nat.add_comm]
    case isFalse.isTrue h₁ h₂ =>
      subst h₂; clear h₁
      conv => rhs; rhs; rw [← Nat.add_zero n]
      rw [Subst.up_get_high_applyr, Subst.cons, Subst.applyr_to_apply, shift_to_parallel 0]; rfl
    case isFalse.isFalse h₁ h₂ =>
      have h := Nat.lt_of_le_of_ne (Nat.le_of_not_lt h₁) (Ne.symm h₂); clear h₁ h₂
      rw [Subst.up_get_low]; exact h
  case binder e ih => rw [subst, Subst.apply, ih]; rfl
  case node x es ih =>
    induction es with
    | nil => simp only [subst, subst.nested, Subst.apply, Subst.apply.nested]
    | cons h' t' ih' =>
      rw [List.foldr] at ih
      simp only [subst, subst.nested, Subst.apply, Subst.apply.nested] at *
      congr 2
      . exact ih.left _ _
      . specialize ih' ih.right
        injection ih'

end Leansubst.Pointwise
