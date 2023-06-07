import Std.Data.Nat.Lemmas
import Leansubst.Defs

/-!
  This file contains equational lemmas related to `Expr`, `Subst`, `ES` and `SE`.
-/

namespace Leansubst.Subst'

section

variable {σ : Type}
variable (s t u : Subst' σ)
variable (i j k : Nat) (x : σ)
variable (e : Expr σ) (es : List (Expr σ))

local notation:arg "⟦" a "⟧" => Quotient.mk (Subst'.setoid σ) a

def up : Nat → Subst' σ → Subst' σ
  | 0,     s => s
  | i + 1, s => cons (.var 0) (comp (up i s) (shift 1))

theorem get_up_low (h : k < j) : (up j (@shift σ i)).get k = .var k := by
  induction j generalizing k with
  | zero => intros; contradiction
  | succ j ih =>
    cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ h) with
    | inl h' =>
      subst h'; rw [up]
      cases k with
      | zero => rfl
      | succ k => rw [get, comp_def, ih k (Nat.lt_succ_self _), apply]
    | inr h' =>
      rw [up]
      cases k with
      | zero => rfl
      | succ k =>
        specialize ih _ (Nat.le_of_lt_succ h)
        rw [get, comp_def, ih, apply]

theorem get_up_high (h : j ≤ k) : (up j (@shift σ i)).get k = .var (k + i) := by
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
      rw [ih _ _ hd, apply, Nat.succ_add]

theorem comp_eqv_comps_special : comp (up j (shift i)) (shift 1) ≈ (comps (up j (shift i)) 1 : Subst' σ) := by
  intros k
  rw [comp_def, comps_def]
  cases Nat.lt_sum_ge k j with
  | inl h =>
    rw [get_up_low _ _ _ h, apply, applys]
    split
    case inl _ => rfl
    case inr h => exact (h (Nat.zero_le _)).elim
  | inr h =>
    rw [get_up_high _ _ _ h, apply, applys]
    split
    case inl _ => rfl
    case inr h => exact (h (Nat.zero_le _)).elim

/-- We have to show that `applys` actually agrees with `apply shift`. -/
theorem applys_def : applys j i e = apply (up j (shift i)) e := by
  revert j
  -- Induction on `e`.
  apply @Expr.recOn _
    (fun e => ∀ j, applys j i e = apply (up j (shift i)) e)
    (List.foldr (fun e etc => (∀ j, applys j i e = apply (up j (shift i)) e) ∧ etc) True)
    <;> intros <;> try trivial
  case var k j =>
    induction j generalizing k with
    | zero =>
      rw [up, applys]
      split
      case inl _ => rw [apply]
      case inr h => exact (h (Nat.zero_le _)).elim
    | succ j ih =>
      simp only [up, applys, apply_var] at *
      cases k with
      | zero => (split <;> try contradiction); rfl
      | succ k =>
        simp only [get, comp_def, ← ih]
        split <;> rename_i h
        rotate_right; have h : ¬j ≤ k := fun h' => (h (Nat.succ_le_succ h')).elim
        rotate_right; have h := Nat.le_of_succ_le_succ h
        all_goals (split <;> try contradiction)
        case inl => rw [apply, Nat.succ_add]
        case inr => rw [apply]
  case binder e ih j =>
    rw [applys, apply, ih, up]
    congr 1
    have h := comp_eqv_comps_special i j (σ := σ)
    have h' : (.cons (.var 0) ⟦comp (up j (shift i)) (shift 1)⟧ : Subst σ) e =
              (.cons (.var 0) ⟦comps (up j (shift i)) 1⟧ : Subst σ) e := by rw [Quotient.sound h]
    exact h'
  case node x es ih j =>
    induction es with
    | nil => rw [applys, apply, apply.nested]; rfl
    | cons h' t' ih' =>
      rw [List.foldr] at ih
      rw [applys, applys.nested, apply, apply.nested]
      congr
      . exact ih.left _
      . specialize ih' ih.right
        rw [applys, apply] at ih'
        injection ih'

theorem apply_apply : t (s e) = (comp s t) e := by
  sorry

theorem id_apply : (id σ) e = e := by
  sorry

end

end Subst'

namespace Subst

@[simp] theorem shift_wrap (n : Nat) : ⟦Subst'.shift n⟧ = Subst.shift σ n := rfl
@[simp] theorem cons_wrap (e : Expr σ) (s : Subst' σ) : ⟦Subst'.cons e s⟧ = Subst.cons e ⟦s⟧ := rfl
@[simp] theorem id_wrap : ⟦Subst'.id σ⟧ = Subst.id σ := rfl

@[simp] theorem get_wrap (s : Subst' σ) (i : Nat) : Subst'.get s i = Subst.get ⟦s⟧ i := rfl
@[simp] theorem apply_wrap (s : Subst' σ) : Subst'.apply s = Subst.apply ⟦s⟧ := rfl
@[simp] theorem comps_wrap (s : Subst' σ) (n : Nat) : ⟦Subst'.comps s n⟧ = Subst.comps ⟦s⟧ n := rfl
@[simp] theorem comp_wrap (s t : Subst' σ) : ⟦Subst'.comp s t⟧ = Subst.comp ⟦s⟧ ⟦t⟧ := rfl

section

variable {σ : Type}
variable (s t u : Subst σ)
variable (i j k : Nat) (x : σ)
variable (e : Expr σ) (es : List (Expr σ))

local notation:arg "⟦" a "⟧" => Quotient.mk (Subst'.setoid σ) a

@[simp]
theorem get_zero : (cons e s).get 0 = e := by
  induction s using Quotient.ind
  rw [← cons_wrap, ← get_wrap]
  rfl

@[simp]
theorem get_succ : (cons e s).get (i + 1) = s.get i := by
  induction s using Quotient.ind
  rw [← cons_wrap, ← get_wrap]
  rfl

@[simp]
theorem shift_zero : shift σ 0 = id σ := by
  rfl

@[simp]
theorem shift_succ_succ : shift σ (i + 1 + 1) = comp (shift σ (i + 1)) (shift σ 1) := by
  simp only [← shift_wrap, ← comp_wrap]
  apply Quotient.sound
  intros j
  rfl

@[simp]
theorem comps_expand : comps s i = comp s (shift σ i) := by
  induction s using Quotient.ind
  rw [← comps_wrap, ← shift_wrap, ← comp_wrap]
  apply Quotient.sound
  intros j
  rw [Subst'.comps_def, Subst'.comp_def, Subst'.applys_def]
  rfl

@[simp]
theorem apply_var : s (.var i) = s.get i := by
  induction s using Quotient.ind
  rw [← apply_wrap, ← get_wrap, Subst'.apply_var]

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
  intros j
  rw [Subst'.id, Subst'.comp_def, Subst'.get, Subst'.apply_var]
  rfl

@[simp]
theorem comp_id : comp s (id σ) = s := by
  induction s using Quotient.ind; rename_i s
  rw [← id_wrap, ← comp_wrap]
  apply Quotient.sound
  intros j
  rw [Subst'.comp_def, apply_wrap, id_wrap, id_apply]

@[simp]
theorem shift_comp_cons : comp (shift σ 1) (cons e s) = s := by
  induction s using Quotient.ind; rename_i s
  rw [← cons_wrap, ← shift_wrap, ← comp_wrap]
  apply Quotient.sound
  intros j
  rw [Subst'.comp_def, Subst'.get, Subst'.apply, Subst'.apply_var]

@[simp]
theorem cons_comp : comp (cons e s) t = cons (t e) (comp s t) := by
  induction s using Quotient.ind; rename_i s
  induction t using Quotient.ind; rename_i t
  simp only [← apply_wrap, ← cons_wrap, ← comp_wrap]
  apply Quotient.sound
  intros j
  cases j with
  | zero => rw [Subst'.comp_def, Subst'.get]; rfl
  | succ j => rw [Subst'.comp_def, Subst'.get, Subst'.get, Subst'.comp_def]

@[simp]
theorem comp_assoc : comp (comp s t) u = comp s (comp t u) := by
  induction s using Quotient.ind; rename_i s
  induction t using Quotient.ind; rename_i t
  induction u using Quotient.ind; rename_i u
  simp only [← comp_wrap]
  apply Quotient.sound
  intros j
  simp only [Subst'.comp_def, Subst'.apply]
  simp only [get_wrap, apply_wrap, apply_apply, comp_wrap]

@[simp]
theorem apply_zero_cons_shift_comp : cons (s (.var 0)) (comp (shift σ 1) s) = s := by
  induction s using Quotient.ind; rename_i s
  rw [← apply_wrap, Subst'.apply_var, ← shift_wrap, ← comp_wrap, ← cons_wrap]
  apply Quotient.sound
  intros j
  cases j with
  | zero => rfl
  | succ j => rw [Subst'.get, Subst'.comp_def, Subst'.get, Subst'.apply_var]

@[simp]
theorem zero_cons_shift : cons (.var 0) (shift σ 1) = id σ := by
  rw [← shift_wrap, ← id_wrap, ← cons_wrap]
  apply Quotient.sound
  intros j
  cases j with
  | zero => rfl
  | succ => rfl

/-
example : comp (shift σ 1) (id σ) = shift σ 1 := by
  simp
-/

end

end Leansubst.Subst
