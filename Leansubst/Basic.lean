import Std.Data.Nat.Lemmas
import Leansubst.Defs

/-!
  This file contains equational lemmas related to `Expr`, `Subst`, `ES` and `SE`.
-/

namespace Leansubst.Subst'

variable {σ : Type}

local notation:arg "⟦" a "⟧" => Quotient.mk (Subst'.setoid σ) a

variable (s t u : Subst' σ)
variable (i j k : Nat) (x : σ)
variable (e : Expr σ) (es : List (Expr σ))

/-- Extensionally equal substitutions have the same effect. -/
theorem eqv_apply : s ≈ t → s e = t e := by
  intros h
  rw [Subst.apply.respects s t h]

/-- Auxiliary function. -/
def up : Nat → Subst' σ → Subst' σ
  | 0,     s => s
  | i + 1, s => cons (.var 0) (comp (up i s) (shift 1))

/-- Auxiliary function. -/
def drop : Nat → Subst' σ → Subst' σ
  | 0,     s => s
  | i + 1, s => comp (shift 1) (drop i s)

/-- Accessing higher entries of `up shift`. -/
theorem up_shift_get_high (h : j ≤ k) : (up j (@shift σ i)).get k = .var (k + i) := by
  have ⟨d, hd⟩ := Nat.le.dest h; clear h
  induction j generalizing k d with
  | zero => rfl
  | succ j ih =>
    rw [up]
    cases k with
    | zero => cases d <;> contradiction
    | succ k =>
      rw [get, comp_def]
      rw [Nat.succ_add] at hd; injection hd with hd
      rw [ih _ _ hd, apply, get, Nat.succ_add]

/-- Accessing lower entries of `up`. -/
theorem up_get_low (h : k < j) : (up j s).get k = .var k := by
  induction j generalizing k with
  | zero => intros; contradiction
  | succ j ih =>
    cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ h) with
    | inl h' =>
      subst h'; rw [up]
      cases k with
      | zero => rfl
      | succ k => rw [get, comp_def, ih k (Nat.lt_succ_self _), apply, get]
    | inr h' =>
      rw [up]
      cases k with
      | zero => rfl
      | succ k =>
        specialize ih _ (Nat.le_of_lt_succ h)
        rw [get, comp_def, ih, apply, get]

/-- Lemma: `applys` agrees with `apply up shift` on variables. -/
theorem applys_var : applys j i (.var k) = apply (up j (@shift σ i)) (.var k) := by
  induction j generalizing k with
  | zero =>
    rw [up, applys]
    split
    case inl _ => rw [apply, get]
    case inr h => exact (h (Nat.zero_le _)).elim
  | succ j ih =>
    simp only [up, apply, applys] at *
    cases k with
    | zero => (split <;> try contradiction); rfl
    | succ k =>
      simp only [get, comp_def, ← ih]
      split <;> rename_i h
      rotate_right; have h : ¬j ≤ k := fun h' => (h (Nat.succ_le_succ h')).elim
      rotate_right; have h := Nat.le_of_succ_le_succ h
      all_goals (split <;> try contradiction)
      case inl => rw [apply, get, Nat.succ_add]
      case inr => rw [apply, get]

/-- Lemma: `comps` agrees with `comp shift` for LHS in the form of `up shift`.  -/
theorem comps_eqv_comp_special : comps (up j (shift i)) 1 ≈ comp (up j (shift i)) (@shift σ 1) := by
  intros k
  rw [comp_def, comps_def]
  cases Nat.lt_sum_ge k j with
  | inl h =>
    rw [up_get_low _ _ _ h, apply, applys]
    split
    case inl _ => rfl
    case inr h => exact (h (Nat.zero_le _)).elim
  | inr h =>
    rw [up_shift_get_high _ _ _ h, apply, applys]
    split
    case inl _ => rfl
    case inr h => exact (h (Nat.zero_le _)).elim

/-- Now we have that `applys` actually agrees with `apply up shift`. -/
theorem applys_def : applys j i e = apply (up j (shift i)) e := by
  revert j
  -- Induction on `e`.
  let motive := fun (e : Expr σ) => ∀ j, applys j i e = apply (up j (shift i)) e
  apply @Expr.recOn _ (fun e => motive e) (List.foldr (fun e etc => motive e ∧ etc) True)
    <;> intros <;> (try trivial) <;> intros j
  case var k => exact applys_var _ _ _
  case binder e ih =>
    rw [applys, apply, ih, up, eqv_apply]
    intros k
    cases k with
    | zero => rfl
    | succ => rw [get, get, comps_eqv_comp_special]
  case node x es ih =>
    induction es with
    | nil => rw [applys, apply, apply.nested]; rfl
    | cons h' t' ih' =>
      rw [List.foldr] at ih
      rw [applys, applys.nested, apply, apply.nested]
      congr 2
      . exact ih.left _
      . specialize ih' ih.right
        rw [applys, apply] at ih'
        injection ih'

/-- Now we have that `comps` actually agrees with `comp shift`. -/
theorem comps_eqv_comp : comps s i ≈ comp s (shift i) := by
  intros k
  rw [comp_def, comps_def, applys_def, up]

/-- Applying the identity substitution. -/
theorem id_apply : (id σ) e = e := by
  -- Induction on `e`.
  apply @Expr.recOn _ (fun e => (id σ) e = e) (List.foldr (fun e etc => (id σ) e = e ∧ etc) True)
    <;> intros <;> (try trivial)
  case var i => rw [id, apply]; rfl
  case binder e ih =>
    conv => rhs; rw [← ih]
    rw [id, apply, comps, eqv_apply]
    intros k
    cases k <;> rfl
  case node x es ih =>
    induction es with
    | nil => rw [id, apply, apply.nested]
    | cons h' t' ih' =>
      rw [List.foldr] at ih
      rw [apply, apply.nested]
      congr 2
      . exact ih.left
      . specialize ih' ih.right
        rw [id, apply] at ih'
        injection ih'

/-- Accessing higher entries of `up`. -/
theorem up_get_high : (up j s).get (j + k) = apply (shift j) (s.get k) := by
  induction j generalizing k with
  | zero => rw [up, Nat.zero_add, ← id, id_apply]
  | succ j ih =>
    rw [up, Nat.succ_add, get, comp_def, ih]
    sorry

theorem up_apply_up_shift_apply : (up (i + 1) s) ((up i (shift 1)) e) = (up i (shift 1)) ((up i s) e) := by
  revert s
  -- Induction on `e`.
  let motive := fun (e : Expr σ) => ∀ i s, (up (i + 1) s) ((up i (shift 1)) e) = (up i (shift 1)) ((up i s) e)
  apply @Expr.recOn _ (fun e => motive e) (List.foldr (fun e etc => motive e ∧ etc) True)
    <;> intros <;> (try trivial) <;> intros i s
  case var j =>
    simp only [get, apply, comp_def]
    cases Nat.lt_sum_ge j i with
    | inl h => have h' := Nat.lt_succ_of_lt h; simp only [up_get_low _ _ _ h, up_get_low _ _ _ h', apply]
    | inr h =>
      have ⟨d, hd⟩ := Nat.le.dest h; subst hd; clear h
      simp only [up_get_high _ _ _]
      rw [get, apply, get, apply, Nat.add_assoc, Nat.add_comm 1 i, Nat.add_comm d (i + 1), up_get_high]
      sorry
  case binder e ih =>
    simp only [apply]
    congr 1
    have h : ∀ (t : Subst' σ), cons (Expr.var 0) (comps t 1) ≈ cons (Expr.var 0) (comp t (shift 1)) := by
      intros t k
      cases k with
      | zero => rfl
      | succ => rw [get]; exact comps_eqv_comp _ _ _
    simp only [eqv_apply _ _ _ (h _)]; clear h
    exact ih _ _
  case node x es ih =>
    induction es with
    | nil => simp only [apply, apply.nested] 
    | cons h' t' ih' =>
      rw [List.foldr] at ih
      simp only [apply, apply.nested]
      congr 2
      . exact ih.left _ _
      . specialize ih' ih.right
        simp only [apply] at ih'
        injection ih'

/-- Applying composition of substitutions. -/
theorem apply_apply : t (s e) = (comp s t) e := by
  -- Induction on `e`.
  let motive := fun (e : Expr σ) => ∀ t s, t (s e) = (comp s t) e
  apply @Expr.recOn _ (fun e => motive e) (List.foldr (fun e etc => (motive e) ∧ etc) True)
    <;> intros <;> (try trivial) <;> intros t s
  case var i => simp only [comp_def, apply]
  case binder e ih =>
    simp only [apply]
    rw [ih, eqv_apply]
    intros k
    cases k with
    | zero => simp only [get, comp_def, apply]
    | succ k =>
      simp only [get, comp_def, comps_def, applys_def, up]
      have h : cons (Expr.var 0) (comps t 1) ≈ cons (Expr.var 0) (comp t (shift 1)) := by
        intros k
        cases k with
        | zero => rfl
        | succ => rw [get]; exact comps_eqv_comp _ _ _
      rw [eqv_apply _ _ _ h]; clear h
      exact up_apply_up_shift_apply _ 0 _
  case node x es ih =>
    -- TODO: make a tactic to solve this case...
    induction es with
    | nil => simp only [apply, apply.nested] 
    | cons h' t' ih' =>
      rw [List.foldr] at ih
      simp only [apply, apply.nested]
      congr 2
      . exact ih.left _ _
      . specialize ih' ih.right
        simp only [apply] at ih'
        injection ih'

end Subst'

namespace Subst

variable {σ : Type}

local notation:arg "⟦" a "⟧" => Quotient.mk (Subst'.setoid σ) a

@[simp] theorem shift_wrap (n : Nat) : ⟦Subst'.shift n⟧ = Subst.shift σ n := rfl
@[simp] theorem cons_wrap (e : Expr σ) (s : Subst' σ) : ⟦Subst'.cons e s⟧ = Subst.cons e ⟦s⟧ := rfl
@[simp] theorem id_wrap : ⟦Subst'.id σ⟧ = Subst.id σ := rfl

@[simp] theorem get_wrap (s : Subst' σ) (i : Nat) : Subst'.get s i = Subst.get ⟦s⟧ i := rfl
@[simp] theorem apply_wrap (s : Subst' σ) : Subst'.apply s = Subst.apply ⟦s⟧ := rfl
@[simp] theorem comps_wrap (s : Subst' σ) (n : Nat) : ⟦Subst'.comps s n⟧ = Subst.comps ⟦s⟧ n := rfl
@[simp] theorem comp_wrap (s t : Subst' σ) : ⟦Subst'.comp s t⟧ = Subst.comp ⟦s⟧ ⟦t⟧ := rfl

variable (s t u : Subst σ)
variable (i j k : Nat) (x : σ)
variable (e : Expr σ) (es : List (Expr σ))

@[simp]
theorem get_zero : (cons e s).get 0 = e := by
  induction s using Quotient.ind
  rw [← cons_wrap, ← get_wrap]; rfl

@[simp]
theorem get_succ : (cons e s).get (i + 1) = s.get i := by
  induction s using Quotient.ind
  rw [← cons_wrap, ← get_wrap]; rfl

@[simp]
theorem shift_zero : shift σ 0 = id σ := rfl

@[simp]
theorem shift_succ_succ : shift σ (i + 1 + 1) = comp (shift σ (i + 1)) (shift σ 1) := by
  simp only [← shift_wrap, ← comp_wrap]
  apply Quotient.sound
  intros k; rfl

@[simp]
theorem comps_expand : comps s i = comp s (shift σ i) := by
  induction s using Quotient.ind
  rw [← comps_wrap, ← shift_wrap, ← comp_wrap]
  apply Quotient.sound
  intros k
  rw [Subst'.comps_def, Subst'.comp_def, Subst'.applys_def]; rfl

@[simp]
theorem apply_var : s (.var i) = s.get i := by
  induction s using Quotient.ind
  rw [← apply_wrap, ← get_wrap, Subst'.apply]

@[simp]
theorem apply_binder : s (.binder e) = .binder ((cons (.var 0) (comp s (shift σ 1))) e) := by
  induction s using Quotient.ind
  rw [← apply_wrap, Subst'.apply]
  simp only [apply_wrap, cons_wrap, comps_wrap, comps_expand]

@[simp]
theorem apply_node : s (.node x es) = .node x (es.map s) := by
  induction s using Quotient.ind
  induction es with
  | nil => rw [List.map, ← apply_wrap, Subst'.apply, Subst'.apply.nested]
  | cons h t ih =>
    rw [List.map, ← apply_wrap, Subst'.apply, Subst'.apply.nested]
    rw [← apply_wrap, Subst'.apply] at ih
    congr; injection ih

@[simp]
theorem apply_apply : t (s e) = (comp s t) e := by
  induction s using Quotient.ind; rename_i s
  induction t using Quotient.ind; rename_i t
  simp only [← comp_wrap, ← apply_wrap]
  exact Subst'.apply_apply _ _ _

@[simp]
theorem id_apply : (id σ) e = e := by
  rw [← id_wrap, ← apply_wrap]
  rw [Subst'.id]
  exact Subst'.id_apply _

@[simp]
theorem id_comp : comp (id σ) s = s := by
  induction s using Quotient.ind
  rw [← id_wrap, ← comp_wrap]
  apply Quotient.sound
  intros k
  rw [Subst'.id, Subst'.comp_def, Subst'.get, Subst'.apply]; rfl

@[simp]
theorem comp_id : comp s (id σ) = s := by
  induction s using Quotient.ind; rename_i s
  rw [← id_wrap, ← comp_wrap]
  apply Quotient.sound
  intros k
  rw [Subst'.comp_def, apply_wrap, id_wrap, id_apply]

@[simp]
theorem shift_comp_cons : comp (shift σ 1) (cons e s) = s := by
  induction s using Quotient.ind; rename_i s
  rw [← cons_wrap, ← shift_wrap, ← comp_wrap]
  apply Quotient.sound
  intros k
  rw [Subst'.comp_def, Subst'.get, Subst'.apply, Subst'.get]

@[simp]
theorem cons_comp : comp (cons e s) t = cons (t e) (comp s t) := by
  induction s using Quotient.ind; rename_i s
  induction t using Quotient.ind; rename_i t
  simp only [← apply_wrap, ← cons_wrap, ← comp_wrap]
  apply Quotient.sound
  intros k
  cases k with
  | zero => rw [Subst'.comp_def, Subst'.get]; rfl
  | succ => rw [Subst'.comp_def, Subst'.get, Subst'.get, Subst'.comp_def]

@[simp]
theorem comp_assoc : comp (comp s t) u = comp s (comp t u) := by
  induction s using Quotient.ind; rename_i s
  induction t using Quotient.ind; rename_i t
  induction u using Quotient.ind; rename_i u
  simp only [← comp_wrap]
  apply Quotient.sound
  intros k
  simp only [Subst'.comp_def, Subst'.apply]
  simp only [get_wrap, apply_wrap, apply_apply, comp_wrap]

@[simp]
theorem apply_zero_cons_shift_comp : cons (s (.var 0)) (comp (shift σ 1) s) = s := by
  induction s using Quotient.ind; rename_i s
  rw [← apply_wrap, Subst'.apply, ← shift_wrap, ← comp_wrap, ← cons_wrap]
  apply Quotient.sound
  intros k
  cases k with
  | zero => rfl
  | succ => rw [Subst'.get, Subst'.comp_def, Subst'.get, Subst'.apply]

@[simp]
theorem zero_cons_shift : cons (.var 0) (shift σ 1) = id σ := by
  rw [← shift_wrap, ← id_wrap, ← cons_wrap]
  apply Quotient.sound
  intros k; cases k <;> rfl

/-
example : comp (shift σ 1) (id σ) = shift σ 1 := by
  simp
-/

end Leansubst.Subst
