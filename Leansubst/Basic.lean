import Std.Data.Nat.Lemmas
import Leansubst.Defs

/-!
  This file contains equational lemmas related to `Expr`, `Subst`, `ES` and `SE`.
-/

namespace Leansubst.Subst

variable {σ : Type}

variable (s t u : Subst σ)
variable (i j k : Nat) (x : σ)
variable (e : Expr σ) (es : List (Expr σ))

/-- `applyr` agrees with `apply` for renamings. -/
@[simp high]
theorem applyr_def (r) : @applyr σ r = apply (.var ∘ r) := by
  apply funext; intros e; revert r
  -- Induction on `e`.
  let motive := fun (e : Expr σ) => ∀ r, applyr r e = apply (.var ∘ r) e
  apply @Expr.recOn _ (fun e => motive e) (List.foldr (fun e etc => motive e ∧ etc) True)
    <;> intros <;> (try trivial) <;> intros r
  case var k => rw [applyr, apply]; rfl
  case binder e ih =>
    rw [applyr, apply]; congr 2; rw [ih]
    suffices h : (.var ∘ fun | 0 => 0 | i + 1 => r i + 1) =
                 (cons (.var 0) (compr (.var ∘ r) (fun x => x + 1))) by rw [← h]; rfl
    apply funext; intros i
    cases i with
    | zero => rfl
    | succ i => simp only [Function.comp, cons, compr, applyr]
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

def up : Nat → Subst σ → Subst σ
  | 0,     s => s
  | i + 1, s => cons (.var 0) (compr (up i s) (1 + .))

theorem gg : apply (up 1 s) (applyr (1 + .) e) = applyr (1 + .) (apply s e) := by
  -- Induction on `e`.
  let motive := fun (e : Expr σ) => ∀ s, @apply σ (up 1 s) (applyr (1 + .) e) = applyr (1 + .) (apply s e)
  apply @Expr.recOn _ (fun e => motive e) (List.foldr (fun e etc => motive e ∧ etc) True)
    <;> intros <;> (try trivial) <;> intros s
  case var k =>
    simp only [Function.comp, apply]
  case binder e ih =>
    simp [applyr_def, apply] at *
    
    rw [ih]
    suffices h : (.var ∘ fun | 0 => 0 | i + 1 => r i + 1) =
                 (cons (.var 0) (compr (.var ∘ r) (fun x => x + 1))) by rw [← h]; rfl
    apply funext; intros i
    cases i with
    | zero => rfl
    | succ i => simp only [Function.comp, cons, compr, applyr]
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

/-!
  Instructions for the `simp` tactic.
  These should also be a complete set of equational axioms.
-/

@[simp]
theorem get_zero : (cons e s) 0 = e := rfl

@[simp]
theorem get_succ : (cons e s) (i + 1) = s i := rfl

@[simp]
theorem shift_wrap_left : .var ∘ (i + .) = shift σ i := rfl

@[simp]
theorem shift_wrap_right : .var ∘ (. + i) = shift σ i := by
  apply funext; intros k; rw [Function.comp, Nat.add_comm]; rfl

@[simp]
theorem shift_zero : shift σ 0 = id σ := by
  apply funext; intros i
  rw [id, shift, Nat.zero_add]

@[simp]
theorem shift_succ_succ : shift σ (i + 1 + 1) = comp (shift σ (i + 1)) (shift σ 1) := by
  apply funext; intros k
  simp only [shift, comp, apply]
  conv => lhs; rw [Nat.add_comm i 1]
  rw [Nat.add_assoc 1, Nat.add_assoc 1]

@[simp]
theorem apply_var : apply s (.var i) = s i := by
  rw [apply]

@[simp]
theorem apply_binder : apply s (.binder e) = .binder (apply (cons (.var 0) (comp s (shift σ 1))) e) := by
  rw [apply]
  simp only [compr_def, shift_wrap_right, comp_def]

@[simp]
theorem apply_node : apply s (.node x es) = .node x (es.map (apply s)) := by
  induction es with
  | nil => rw [List.map, apply, apply.nested]
  | cons h t ih => rw [List.map, apply, apply.nested] at *; congr 2; injection ih

@[simp]
theorem apply_apply : apply t (apply s e) = apply (comp s t) e := by
  rw [comp_def]
  revert t s
  -- Induction on `e`.
  let motive := fun (e : Expr σ) => ∀ s t, @apply σ t (apply s e) = (apply (apply t ∘ s)) e
  apply @Expr.recOn _ (fun e => motive e) (List.foldr (fun e etc => motive e ∧ etc) True)
    <;> intros <;> (try trivial) <;> intros s t
  case var k => simp only [Function.comp, apply]
  case binder e ih =>
    simp only [Function.comp, apply]
    rw [ih]
    simp [Function.comp]
    suffices h :
        apply (cons (.var 0) (apply (shift _ 1) ∘ t)) ∘ cons (.var 0) (apply (shift _ 1) ∘ s) =
        cons (.var 0) (apply (shift _ 1) ∘ apply t ∘ s) by rw [h]
    apply funext; intros i
    cases i with
    | zero => rfl
    | succ i =>
      suffices h : ∀ e,
          apply (cons (.var 0) (compr t (1 + .))) (applyr (1 + .) e) =
          applyr (1 + .) (apply t e) by
        rw [applyr_def, compr_def] at h; exact h (s i)
      exact gg _
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
theorem id_apply : apply (id σ) e = e := by
  sorry

@[simp]
theorem id_comp : comp (id σ) s = s := by
  sorry

@[simp]
theorem comp_id : comp s (id σ) = s := by
  sorry

@[simp]
theorem shift_comp_cons : comp (shift σ 1) (cons e s) = s := by
  sorry

@[simp]
theorem cons_comp : comp (cons e s) t = cons (apply t e) (comp s t) := by
  sorry

@[simp]
theorem comp_assoc : comp (comp s t) u = comp s (comp t u) := by
  sorry

@[simp]
theorem apply_zero_cons_shift_comp : cons (apply s (.var 0)) (comp (shift σ 1) s) = s := by
  sorry

@[simp]
theorem zero_cons_shift : cons (.var 0) (shift σ 1) = id σ := by
  sorry

/-
example : comp (shift σ 1) (id σ) = shift σ 1 := by
  simp
-/

end Leansubst.Subst
