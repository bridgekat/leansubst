import Leansubst.Defs

namespace Leansubst.Renaming

/-- Extensional equivalence of renamings. -/
def eqv (s : Renaming) (t : Renaming) : Prop :=
  ∀ i, s.get i = t.get i

theorem eqv.refl (s : Renaming) : eqv s s :=
  fun _ => .refl _

theorem eqv.symm {s t : Renaming} : eqv s t → eqv t s :=
  fun h i => .symm (h i)

theorem eqv.trans {s t u : Renaming} : eqv s t → eqv t u → eqv s u :=
  fun h₁ h₂ i => .trans (h₁ i) (h₂ i)

instance renamingSetoid : Setoid Renaming where
  r     := eqv
  iseqv := ⟨eqv.refl, eqv.symm, eqv.trans⟩

def Renaming' : Type :=
  Quotient renamingSetoid

scoped notation:arg "⟦" a "⟧" => Quotient.mk renamingSetoid a

def shift' : Nat → Renaming' :=
  fun n => ⟦shift n⟧

def cons' : Nat → Renaming' → Renaming' :=
  fun n => Quotient.lift (fun s => ⟦cons n s⟧) $ by
    intros s t h; apply Quotient.sound; intros i
    cases i with
    | zero => eq_refl
    | succ i => exact h i

def id' : Renaming' :=
  ⟦id⟧

def get' : Renaming' → Nat → Nat :=
  Quotient.lift get $
    fun _ _ h => funext $ fun i => h i

/-- Definition of composition. -/
theorem comp_def (s t : Renaming) : ∀ i, (comp s t).get i = t.get (s.get i) := by
  intros i
  induction s generalizing t i with
  | shift n =>
    induction t generalizing n with
    | shift m => simp [get, comp]; rw [Nat.add_assoc]
    | cons h t ih =>
      cases n with
      | zero => simp [get, comp]
      | succ n => simp [get, comp, ih]
  | cons h s ih =>
    cases i with
    | zero => simp [get, comp, ih]
    | succ i => simp [get, comp, ih]

def comp' : Renaming' → Renaming' → Renaming' :=
  Quotient.lift₂ (fun s t => ⟦comp s t⟧) $ by
    intros s₁ t₁ s₂ t₂ h₁ h₂
    apply Quotient.sound
    intros i
    simp [comp_def, h₁ _, h₂ _]

def apply' {σ} : Renaming' → Expr σ → Expr σ :=
  Quotient.lift apply $ by
    intros s t h; apply funext; intros e; revert s t
    -- Induction on `e`
    apply @Expr.recOn _
      (fun e => ∀ s t, s ≈ t → apply s e = apply t e)
      (fun es => es.foldr (fun e etc => (∀ s t, s ≈ t → apply s e = apply t e) ∧ etc) True)
      <;> intros <;> try trivial
    case var i s t h => simp [apply]; exact h i
    case binder e' ih s t h =>
      simp [apply]
      apply ih
      apply Quotient.exact
      suffices h : cons' 0 (comp' ⟦s⟧ ⟦(shift 1)⟧) = cons' 0 (comp' ⟦t⟧ ⟦(shift 1)⟧) by exact h
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

theorem id_get (i : Nat) : id.get i = i := rfl

theorem id_comp (r : Renaming) : id.comp r ≈ r := by
  intros i
  cases r with
  | shift j => simp [get]
  | cons j r => eq_refl

theorem comp_id (r : Renaming) : r.comp id ≈ r := by
  induction r with
  | shift j => intros i; simp [get, id, Renaming.comp]
  | cons j r ih =>
    intros i
    simp [get, id, Renaming.comp] at *
    suffices h : cons j (comp r (shift 0)) ≈ cons j r by exact h i
    apply Quotient.exact
    suffices h : cons' j ⟦comp r (shift 0)⟧ = cons' j ⟦r⟧ by exact h
    suffices h : ⟦comp r (shift 0)⟧ = ⟦r⟧ by rw [h]
    exact Quotient.sound ih



end Leansubst.Renaming
