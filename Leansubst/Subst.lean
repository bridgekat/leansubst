import Leansubst.Defs
import Leansubst.Renaming

namespace Leansubst.Subst

variable {σ : Type}

/-- Extensional equivalence of substitutions. -/
def eqv (s : Subst σ) (t : Subst σ) : Prop :=
  ∀ i, s.get i = t.get i

theorem eqv.refl (s : Subst σ) : eqv s s :=
  fun _ => .refl _

theorem eqv.symm {s t : Subst σ} : eqv s t → eqv t s :=
  fun h i => .symm (h i)

theorem eqv.trans {s t u : Subst σ} : eqv s t → eqv t u → eqv s u :=
  fun h₁ h₂ i => .trans (h₁ i) (h₂ i)

instance substSetoid : Setoid (Subst σ) where
  r     := eqv
  iseqv := ⟨eqv.refl, eqv.symm, eqv.trans⟩

def Subst' (σ : Type) : Type :=
  Quotient (@substSetoid σ)

scoped notation:arg "⟦" a "⟧" => Quotient.mk _ a

def shift' (σ) : Nat → Subst' σ :=
  fun n => ⟦shift n⟧

def cons' : Expr σ → Subst' σ → Subst' σ :=
  fun e => Quotient.lift (fun s => ⟦cons e s⟧) $ by
    intros s t h; apply Quotient.sound; intros i
    cases i with
    | zero => eq_refl
    | succ i => exact h i

def id' (σ) : Subst' σ :=
  ⟦id σ⟧

def get' : Subst' σ → Nat → Expr σ :=
  Quotient.lift get $
    fun _ _ h => funext $ fun i => h i

/-- Definition of coercion (preserves action). -/
theorem from_renaming_def (σ) (r : Renaming) : ∀ i, (fromRenaming σ r).get i = .var (r.get i) := by
  intros i
  induction r generalizing i with
  | shift n => simp [fromRenaming, get, Renaming.get]
  | cons h t ih =>
    cases i with
    | zero => simp [fromRenaming, get, Renaming.get]
    | succ i => simp [fromRenaming, get, Renaming.get, ih]

/-- Definition of composition with renaming. -/
theorem compr_def (s : Subst σ) (t : Renaming) : ∀ i, (compr s t).get i = t.apply (s.get i) := by
  intros i
  induction s generalizing t i with
  | shift n₁ => simp [Renaming.get, Renaming.comp_def, Renaming.apply, get, compr, from_renaming_def]
  | cons h s ih =>
    cases i with
    | zero => simp [get, comp, ih]
    | succ i => simp [get, comp, ih]

def compr' : Subst' σ → Renaming.Renaming' → Subst' σ :=
  Quotient.lift₂ (fun s t => ⟦compr s t⟧) $ by
    intros s₁ t₁ s₂ t₂ h₁ h₂
    apply Quotient.sound
    intros i
    simp [compr_def]
    suffices h : Renaming.apply' ⟦t₁⟧ (get' ⟦s₁⟧ i) = Renaming.apply' ⟦t₂⟧ (get' ⟦s₂⟧ i) by exact h
    suffices h : ⟦s₁⟧ = ⟦s₂⟧ ∧ ⟦t₁⟧ = ⟦t₂⟧ by rw [h.left, h.right]
    exact ⟨Quotient.sound h₁, Quotient.sound h₂⟩

theorem apply_var_eq_get (s : Subst σ) : ∀ i, s.apply (.var i) = s.get i := by
  intros i
  induction s generalizing i with
  | shift n => simp [apply, get]
  | cons h t ih =>
    cases i with
    | zero => simp [apply, get]
    | succ i => simp [apply, get, ih]

def apply' : Subst' σ → Expr σ → Expr σ :=
  Quotient.lift apply $ by
    intros s t h; apply funext; intros e; revert s t
    -- Induction on `e`
    apply @Expr.recOn _
      (fun e => ∀ s t, s ≈ t → apply s e = apply t e)
      (fun es => es.foldr (fun e etc => (∀ s t, s ≈ t → apply s e = apply t e) ∧ etc) True)
      <;> intros <;> try trivial
    case var i s t h => simp [apply_var_eq_get, h i]
    case binder e' ih s t h =>
      simp [apply]
      apply ih
      apply Quotient.exact
      suffices h : cons' (.var 0) (compr' ⟦s⟧ ⟦.shift 1⟧) = cons' (.var 0) (compr' ⟦t⟧ ⟦.shift 1⟧) by exact h
      suffices h : ⟦s⟧ = ⟦t⟧ by rw [h]
      exact Quotient.sound h
    case node n es ih s t h =>
      simp [apply]
      induction es with
      | nil => simp [apply.applies]
      | cons h' t' ih' =>
        simp [List.foldr] at ih
        simp [apply.applies]
        exact ⟨ih.left _ _ h, ih' ih.right⟩

/-- Definition of composition. -/
theorem comp_def (s t : Subst σ) : ∀ i, (comp s t).get i = t.apply (s.get i) := by
  intros i
  induction s generalizing t i with
  | shift n =>
    induction t generalizing n with
    | shift m => simp [get, comp, apply_var_eq_get]; rw [Nat.add_assoc]
    | cons h t ih =>
      cases n with
      | zero => simp [get, comp, apply_var_eq_get]
      | succ n => simp [get, comp, apply_var_eq_get, ih]
  | cons h s ih =>
    cases i with
    | zero => simp [get, comp, ih]
    | succ i => simp [get, comp, ih]

theorem cons_zero_compr_shift_eqv_id : cons (.var 0) (compr (id σ) (.shift 1)) ≈ id σ := by
  intros i
  cases i with
  | zero => simp [get]
  | succ i => simp [get]

theorem id_get (i : Nat) : (id σ).get i = .var i := rfl

theorem apply_id (e : Expr σ) : (id σ).apply e = e := by
  -- Induction on `e`
  apply @Expr.recOn _
    (fun e => apply (id σ) e = e)
    (fun es => es.foldr (fun e etc => apply (id σ) e = e ∧ etc) True)
    <;> intros <;> try trivial
  case var i => simp [apply_var_eq_get, get]
  case binder e' ih =>
    simp [apply]
    suffices h : apply' ⟦cons (Expr.var 0) (compr (id σ) (Renaming.shift 1))⟧ e' = e' by exact h
    suffices h : ⟦cons (Expr.var 0) (compr (id σ) (Renaming.shift 1))⟧ = id' σ by rw [h]; exact ih
    exact Quotient.sound cons_zero_compr_shift_eqv_id
  case node n es ih =>
    simp [apply]
    induction es with
    | nil => simp [apply.applies]
    | cons h' t' ih' =>
      simp [List.foldr] at ih
      simp [apply.applies]
      exact ⟨ih.left, ih' ih.right⟩

theorem id_comp (r : Subst σ) : (id σ).comp r ≈ r := by
  intros i
  cases r with
  | shift j => simp [get]
  | cons j r => eq_refl

theorem comp_id (r : Subst σ) : r.comp (id σ) ≈ r := by
  induction r with
  | shift j => intros i; simp [get, id, comp]
  | cons j r ih =>
    intros i
    simp [comp, apply_id]
    suffices h : cons j (comp r (shift 0)) ≈ cons j r by exact h i
    apply Quotient.exact
    suffices h : cons' j ⟦comp r (shift 0)⟧ = cons' j ⟦r⟧ by exact h
    suffices h : ⟦comp r (shift 0)⟧ = ⟦r⟧ by rw [h]
    exact Quotient.sound ih



end Leansubst.Subst
