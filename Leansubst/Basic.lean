import Std.Data.Nat.Lemmas
import Leansubst.Defs

/-!
This file contains equational lemmas related to `Expr` and `Subst`.
-/

namespace Leansubst.Subst

variable {σ : Type}

variable (s t u : Subst σ)
variable (i j k : Nat) (x : σ)
variable (e : Expr σ) (es : List (Expr σ))

theorem id_applyr : applyr (.) e = e := by
  -- Induction on `e`.
  apply @Expr.recOn _
      (fun e => applyr (.) e = e)
      (List.foldr (fun e etc => applyr (.) e = e ∧ etc) True)
    <;> intros <;> (try trivial)
  case var i => rw [applyr]
  case binder e ih =>
    conv => lhs; rw [applyr]
    conv => rhs; rw [← ih]
    congr 2; apply funext; intros k; cases k <;> rfl
  case node x es ih =>
    induction es with
    | nil => simp only [applyr, applyr.nested]
    | cons h' t' ih' =>
      rw [List.foldr] at ih
      simp only [applyr, applyr.nested] at *
      congr 2
      . exact ih.left
      . specialize ih' ih.right
        simp only [applyr, applyr.nested] at ih'
        injection ih'

theorem applyr_applyr (s r) : applyr r (applyr s e) = applyr (r ∘ s) e := by
  revert s r
  -- Induction on `e`.
  let motive := fun (e : Expr σ) => ∀ s r, @applyr σ r (applyr s e) = applyr (r ∘ s) e
  apply @Expr.recOn _ (fun e => motive e) (List.foldr (fun e etc => motive e ∧ etc) True)
    <;> intros <;> (try trivial) <;> intros s t
  case var i => rw [applyr, applyr, applyr]; rfl
  case binder e ih =>
    rw [applyr, applyr, applyr, ih]
    congr 2; apply funext; intros k; cases k <;> rfl
  case node x es ih =>
    induction es with
    | nil => simp only [applyr, applyr.nested]
    | cons h' t' ih' =>
      rw [List.foldr] at ih
      simp only [applyr, applyr.nested] at *
      congr 2
      . exact ih.left _ _
      . specialize ih' ih.right
        simp only [applyr, applyr.nested] at ih'
        injection ih'

/-- `applyr` agrees with `apply` for renamings. -/
@[simp high]
theorem applyr_def (r) : @applyr σ r = apply (.var ∘ r) := by
  apply funext; intros e; revert r
  -- Induction on `e`.
  let motive := fun (e : Expr σ) => ∀ r, applyr r e = apply (.var ∘ r) e
  apply @Expr.recOn _ (fun e => motive e) (List.foldr (fun e etc => motive e ∧ etc) True)
    <;> intros <;> (try trivial) <;> intros r
  case var i => rw [applyr, apply]; rfl
  case binder e ih =>
    rw [applyr, apply, ih]
    congr 2; apply funext; intros i
    cases i with
    | zero => rfl
    | succ i => simp only [Function.comp, upr, up, cons, compr, applyr]
  case node x es ih =>
    induction es with
    | nil => rw [applyr, apply, apply.nested]; rfl
    | cons h' t' ih' =>
      rw [List.foldr] at ih
      rw [applyr, applyr.nested, apply, apply.nested]
      congr 2
      . exact ih.left _
      . specialize ih' ih.right
        rw [applyr, apply] at ih'
        injection ih'

/-- `compr` agrees with `comp` for renamings. -/
@[simp high]
theorem compr_def (s r) : @compr σ s r = comp s (.var ∘ r) := by
  apply funext; intros i
  rw [compr, comp, applyr_def]

/-- Accessing higher entries of `upr`. -/
theorem upr_get_high (r) : upr i r (i + j) = r j + i := by
  induction i with
  | zero => rw [Nat.zero_add]; rfl
  | succ i ih => rw [Nat.succ_add, Nat.add_succ, ← ih]; rfl

/-- Accessing lower entries of `upr`. -/
theorem upr_get_low (r) (h : j < i) : (upr i r) j = j := by
  induction i generalizing j with
  | zero => contradiction
  | succ i ih =>
    cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ h) with
    | inl h' =>
      subst h'; rw [upr]
      cases j with
      | zero => rfl
      | succ j => simp only; rw [ih _ (Nat.lt_succ_self _)]
    | inr h' =>
      rw [upr]
      cases j with
      | zero => rfl
      | succ k =>
        simp only
        rw [ih _ (Nat.le_of_lt_succ h)]

/-- Accessing higher entries of `up`. -/
theorem up_get_high : (up i s) (i + j) = applyr (. + i) (s j) := by
  induction i with
  | zero =>
    rw [up, Nat.zero_add, funext Nat.add_zero, id_applyr]
  | succ i ih =>
    rw [up, Nat.succ_add, cons]; simp only
    rw [compr, ih, applyr_applyr]; rfl

/-- Accessing lower entries of `up`. -/
theorem up_get_low (h : j < i) : (up i s) j = .var j := by
  induction i generalizing j with
  | zero => contradiction
  | succ i ih =>
    cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ h) with
    | inl h' =>
      subst h'; rw [up]
      cases j with
      | zero => rfl
      | succ j =>
        rw [cons]; simp only
        rw [compr, ih _ (Nat.lt_succ_self _), applyr]
    | inr h' =>
      rw [up]
      cases j with
      | zero => rfl
      | succ k =>
        rw [cons]; simp only
        rw [compr, ih _ (Nat.le_of_lt_succ h), applyr]

/-- `upr` agrees with `up` for renamings. -/
@[simp high]
theorem upr_def (r) : .var ∘ upr i r = @up σ i (.var ∘ r) := by
  apply funext; intros j
  cases Nat.lt_sum_ge j i with
  | inl h => rw [Function.comp, upr_get_low _ _ _ h, up_get_low _ _ _ h]
  | inr h =>
    have ⟨d, hd⟩ := Nat.le.dest h; subst hd; clear h
    rw [Function.comp, upr_get_high, up_get_high, Function.comp, applyr]

/-- A difficult lemma for proving `apply_apply`... -/
theorem gg : apply (up (i + 1) s) (applyr (upr i (. + 1)) e) = applyr (upr i (. + 1)) (apply (up i s) e) := by
  -- Induction on `e`.
  let motive := fun (e : Expr σ) => ∀ s i,
      @apply σ (up (i + 1) s) (applyr (upr i (. + 1)) e) = applyr (upr i (. + 1)) (apply (up i s) e)
  apply @Expr.recOn _ (fun e => motive e) (List.foldr (fun e etc => motive e ∧ etc) True)
    <;> intros <;> (try trivial) <;> intros s i
  case var j =>
    rw [applyr, apply, apply]
    cases Nat.lt_sum_ge j i with
    | inl h => rw [up_get_low _ _ _ h, applyr, upr_get_low _ _ _ h, up_get_low _ _ _ (Nat.lt_succ_of_lt h)]
    | inr h =>
      have ⟨d, hd⟩ := Nat.le.dest h; subst hd; clear h
      rw [up_get_high, upr_get_high, Nat.add_comm (d + 1), Nat.add_comm d, ← Nat.add_assoc, up_get_high, applyr_applyr]
      congr 1; apply funext; intros j
      rw [Function.comp, Nat.add_comm j i, upr_get_high, Nat.add_comm i 1, Nat.add_assoc]
  case binder e ih =>
    conv => lhs; rw [applyr, apply, up, up, ← up, upr, upr, ← upr]
    have h : s = up 0 s := rfl
    conv => rhs; rw [apply, applyr, h, up, up, ← up, upr, upr, ← upr]
    congr 1
    exact ih _ _
  case node x es ih =>
    induction es with
    | nil => simp only [apply, apply.nested, applyr, applyr.nested]
    | cons h' t' ih' =>
      rw [List.foldr] at ih
      simp only [apply, apply.nested, applyr, applyr.nested] at *
      congr 2
      . exact ih.left _ _
      . specialize ih' ih.right
        simp only [apply, apply.nested, applyr, applyr.nested] at ih'
        injection ih'

/-!
  Instructions for the `simp` tactic.
  These should also be a complete set of equational axioms.
-/

@[simp]
theorem cons_zero : (cons e s) 0 = e := rfl

@[simp]
theorem cons_succ : (cons e s) (i + 1) = s i := rfl

/-- Normalise expanded `applyr`, `compr` and `upr`. -/
@[simp]
theorem shift_wrap_right : .var ∘ (. + i) = shift σ i := rfl

/-- Normalise expanded `applyr`, `compr` and `upr`. -/
@[simp]
theorem shift_wrap_left : .var ∘ (i + .) = shift σ i := by
  apply funext; intros k; rw [Function.comp, Nat.add_comm]; rfl

/-- Normalise `shift n` to either `shift 1` or `id`. -/
@[simp]
theorem shift_zero : shift σ 0 = id σ := by
  apply funext; intros i
  rw [id, shift]; rfl

/-- This must be manually applied... -/
theorem shift_succ : shift σ (i + 1) = comp (shift σ i) (shift σ 1) := by
  apply funext; intros j; rw [shift, comp, shift, apply, shift, Nat.add_assoc]

/-- Normalise `shift n` to either `shift 1` or `id`. -/
@[simp]
theorem shift_succ_succ : shift σ (i + 1 + 1) = comp (shift σ (i + 1)) (shift σ 1) := by
  apply funext; intros j; rw [shift_succ]

@[simp]
theorem apply_var : apply s (.var i) = s i := by
  rw [apply]

@[simp]
theorem apply_binder : apply s (.binder e) = .binder (apply (cons (.var 0) (comp s (shift σ 1))) e) := by
  rw [apply]
  simp only [compr_def, shift_wrap_right, comp_def, up]

@[simp]
theorem apply_node : apply s (.node x es) = .node x (es.map (apply s)) := by
  induction es with
  | nil => rw [List.map, apply, apply.nested]
  | cons h t ih => rw [List.map, apply, apply.nested] at *; congr 2; injection ih

@[simp]
theorem id_apply : apply (id σ) e = e := by
  -- Induction on `e`.
  apply @Expr.recOn _
      (fun e => apply (id σ) e = e)
      (List.foldr (fun e etc => apply (id σ) e = e ∧ etc) True)
    <;> intros <;> (try trivial)
  case var i => rw [apply]; rfl
  case binder e ih =>
    conv => lhs; rw [apply]
    conv => rhs; rw [← ih]
    congr 2; apply funext; intros k
    cases k with
    | zero => rfl
    | succ => simp only [cons, id, compr, applyr, up]
  case node x es ih =>
    induction es with
    | nil => simp only [apply, apply.nested]
    | cons h' t' ih' =>
      rw [List.foldr] at ih
      simp only [apply, apply.nested] at *
      congr 2
      . exact ih.left
      . specialize ih' ih.right
        simp only [apply, apply.nested] at ih'
        injection ih'

@[simp]
theorem apply_apply : apply t (apply s e) = apply (comp s t) e := by
  rw [comp_def]
  revert t s
  -- Induction on `e`.
  let motive := fun (e : Expr σ) => ∀ s t, @apply σ t (apply s e) = (apply (apply t ∘ s)) e
  apply @Expr.recOn _ (fun e => motive e) (List.foldr (fun e etc => motive e ∧ etc) True)
    <;> intros <;> (try trivial) <;> intros s t
  case var i => rw [apply, apply]; rfl
  case binder e ih =>
    rw [apply, apply, apply, ih]
    congr 2; apply funext; intros i
    cases i with
    | zero => rfl
    | succ i => have h := gg t 0; rw [up, upr] at h; exact h (s i)
  case node x es ih =>
    induction es with
    | nil => simp only [apply, apply.nested]
    | cons h' t' ih' =>
      rw [List.foldr] at ih
      simp only [apply, apply.nested] at *
      congr 2
      . exact ih.left _ _
      . specialize ih' ih.right
        simp only [apply, apply.nested] at ih'
        injection ih'

@[simp]
theorem id_comp : comp (id σ) s = s := by
  apply funext; intros i; rw [comp_def, Function.comp, id, apply]

@[simp]
theorem comp_id : comp s (id σ) = s := by
  apply funext; intros i; rw [comp_def, Function.comp, id_apply]

@[simp]
theorem shift_comp_cons : comp (shift σ 1) (cons e s) = s := by
  apply funext; intros i; rw [comp_def, Function.comp, shift, apply]; rfl

@[simp]
theorem cons_comp : comp (cons e s) t = cons (apply t e) (comp s t) := by
  apply funext; intros i; rw [comp_def, Function.comp, comp_def]; cases i <;> rfl

@[simp]
theorem comp_assoc : comp (comp s t) u = comp s (comp t u) := by
  apply funext; intros i; simp only [comp_def, Function.comp, apply_apply]

@[simp]
theorem apply_zero_cons_shift_comp : cons (apply s (.var 0)) (comp (shift σ 1) s) = s := by
  apply funext; intros i; cases i <;> rfl

@[simp]
theorem zero_cons_shift : cons (.var 0) (shift σ 1) = id σ := by
  apply funext; intros i; cases i <;> rfl

end Leansubst.Subst
