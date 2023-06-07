import Std.Data.Nat.Basic
import Std.Tactic.Basic

/-!
  This file contains the definitions of:

  - Expressions: `Expr`;
  - Substitutions: `Subst` (as a quotient of regular substitutions modulo extensional equivalence);
  - Expressions with explicit substitutions and "metavariables": `ES` and `SE`.

  The development roughly follows
  [[1]](https://www.ps.uni-saarland.de/Publications/documents/SchaeferEtAl_2015_Completeness.pdf)
  with some difference in terminology and formalism.
-/

namespace Leansubst

/-!
  First we define expressions *without* explicit substitutions and "metavariables".
  They serve as a semantic model for more complex expressions (so-called "de Bruijn algebra").
-/

/-- Abstract syntax tree using de Bruijn indices. -/
inductive Expr (σ : Type) where
  | var    : Nat →               Expr σ -- Variable in de Bruijn index.
  | binder : Expr σ →            Expr σ -- Binder presence.
  | node   : σ → List (Expr σ) → Expr σ -- Tree node.

/-- Substitutions. -/
inductive Subst' (σ : Type) where
  | shift : Nat →               Subst' σ -- Shift overflow variables up.
  | cons  : Expr σ → Subst' σ → Subst' σ -- Prepend to sequence.

namespace Subst'

/-- Evaluate substitution at a given index. -/
def get : Subst' σ → Nat → Expr σ
  | shift n,  i     => .var (i + n)
  | cons h _, 0     => h
  | cons _ t, i + 1 => get t i

/-- Extensional equivalence of substitutions. -/
instance setoid (σ) : Setoid (Subst' σ) where
  r     := fun s t => ∀ i, s.get i = t.get i
  iseqv :=
    { refl  := fun _ _ => .refl _
      symm  := fun h i => .symm (h i)
      trans := fun h₁ h₂ i => .trans (h₁ i) (h₂ i) }

/-- The identity substitution. -/
def id (σ) : Subst' σ :=
  shift 0

/-- Shift variables with level ≥ `n` by `m` levels. -/
def applys : Nat → Nat → Expr σ → Expr σ
  | n, m, .var i     => if n <= i then .var (i + m) else .var i
  | n, m, .binder e  => .binder (applys (n + 1) m e)
  | n, m, .node x es => .node x (nested n m es)
where nested : Nat → Nat → List (Expr σ) → List (Expr σ)
  | _, _, []      => []
  | n, m, e :: es => applys n m e :: nested n m es

/-- Composition of substitution and shift. -/
def comps : Subst' σ → Nat → Subst' σ
  | shift n,  m => .shift (n + m)
  | cons h t, m => cons (applys 0 m h) (comps t m)

/-- Composition of substitution and shift follows the expected definition. -/
theorem comps_def (s : Subst' σ) (n : Nat) : ∀ i, (comps s n).get i = applys 0 n (s.get i) := by
  intros i
  induction s generalizing n i with
  | shift m =>
    simp only [get, comps, applys]
    split
    case inl => rw [Nat.add_assoc]
    case inr h => exfalso; exact h (Nat.zero_le _)
  | cons h s ih =>
    cases i with
    | zero => simp only [get, ih]
    | succ i => simp only [get, ih]

/-- Applies a substitution on a term. -/
def apply : Subst' σ → Expr σ → Expr σ
  | shift n,  .var i       => .var (i + n)
  | cons h _, .var 0       => h
  | cons _ t, .var (i + 1) => apply t (.var i)
  | s,        .binder e    => .binder (apply (cons (.var 0) (comps s 1)) e)
  | s,        .node n es   => .node n (nested s es)
where nested : Subst' σ → List (Expr σ) → List (Expr σ)
  | _, []      => []
  | s, e :: es => apply s e :: nested s es
termination_by
  apply s e   => (sizeOf e, sizeOf s)
  nested s es => (sizeOf es, sizeOf s)

/-- Applying a substitution on a variable is equal to `get`. -/
theorem apply_var (s : Subst' σ) : ∀ i, s.apply (.var i) = s.get i := by
  intros i
  induction s generalizing i with
  | shift n => simp only [apply, get]
  | cons h t ih =>
    cases i with
    | zero => simp [apply, get]
    | succ i => simp only [apply, get, ih]

/-- Composition of substitutions. -/
def comp : Subst' σ → Subst' σ → Subst' σ
  | shift n,       shift m  => shift (n + m)
  | shift 0,       cons h t => cons h t
  | shift (n + 1), cons _ t => comp (shift n) t
  | cons h t,      r        => cons (r.apply h) (comp t r)

/-- Composition of substitutions follows the expected definition. -/
theorem comp_def (s t : Subst' σ) : ∀ i, (comp s t).get i = t.apply (s.get i) := by
  intros i
  induction s generalizing t i with
  | shift n =>
    induction t generalizing n with
    | shift m => simp only [get, comp, apply_var]; rw [Nat.add_assoc]
    | cons h t ih =>
      cases n with
      | zero => simp [get, comp, apply_var]
      | succ n => simp [get, comp, apply_var, ih]
  | cons h s ih =>
    cases i with
    | zero => simp only [get, comp, ih]
    | succ i => simp only [get, comp, ih]

/-- Now we can write `s t` for applying substitution `s` on term `t`. -/
instance : CoeFun (Subst' σ) (fun _ => Expr σ → Expr σ) where
  coe := apply

end Subst'

/-- Substitution modulo extensional equivalence. -/
def Subst (σ : Type) : Type :=
  Quotient (Subst'.setoid σ)

namespace Subst

local notation:arg "⟦" a "⟧" => Quotient.mk (Subst'.setoid _) a

/-- Evaluate substitution at a given index. -/
def get : Subst σ → Nat → Expr σ :=
  Quotient.lift Subst'.get $
    fun _ _ h => funext $ fun i => h i

/-- Lifted constructor `shift`. -/
def shift (σ) : Nat → Subst σ :=
  fun n => ⟦Subst'.shift n⟧

/-- Lifted constructor `cons`. -/
def cons : Expr σ → Subst σ → Subst σ :=
  fun e => Quotient.lift (fun s => ⟦Subst'.cons e s⟧) $ by
    intros s t h; apply Quotient.sound; intros i
    cases i with
    | zero => eq_refl
    | succ i => exact h i

/-- Lifted constructor `id`. -/
def id (σ) : Subst σ :=
  ⟦Subst'.id σ⟧

/-- Composition of substitution and shift. -/
def comps : Subst σ → Nat → Subst σ :=
  Quotient.lift (fun s n => ⟦Subst'.comps s n⟧) respects
where
  respects (s t : Subst' σ) (h : s ≈ t) := by
    apply funext
    intros n
    apply Quotient.sound
    intros i
    simp [Subst'.comps_def, h i]

/-- Applies a substitution on a term. -/
def apply : Subst σ → Expr σ → Expr σ :=
  Quotient.lift Subst'.apply respects
where
  respects (s t : Subst' σ) (h : s ≈ t) : s.apply = t.apply := by
    apply funext; intros e; revert s t
    -- Induction on `e`.
    apply @Expr.recOn _
      (fun e => ∀ s t : Subst' σ, s ≈ t → s.apply e = t.apply e)
      (List.foldr (fun e etc => (∀ s t : Subst' σ, s ≈ t → s.apply e = t.apply e) ∧ etc) True)
      <;> intros <;> try trivial
    case var i s t h => simp only [Subst'.apply_var, h i]
    case binder e' ih s t h =>
      simp [Subst'.apply]
      apply ih
      apply Quotient.exact
      suffices h : cons (.var 0) (comps ⟦s⟧ 1) = cons (.var 0) (comps ⟦t⟧ 1) by exact h
      suffices h : ⟦s⟧ = ⟦t⟧ by rw [h]
      exact Quotient.sound h
    case node n es ih s t h =>
      simp [Subst'.apply]
      induction es with
      | nil => simp only [Subst'.apply.nested]
      | cons h' t' ih' =>
        simp only [List.foldr] at ih
        simp [Subst'.apply.nested]
        exact ⟨ih.left _ _ h, ih' ih.right⟩

/-- Composition of substitutions. -/
def comp : Subst σ → Subst σ → Subst σ :=
  Quotient.lift₂ (fun s t => ⟦Subst'.comp s t⟧) respects
where
  respects (s₁ t₁ s₂ t₂ : Subst' σ) (h₁ : s₁ ≈ s₂) (h₂ : t₁ ≈ t₂) : _ := by
    apply Quotient.sound
    intros i
    simp [Subst'.comp_def]
    suffices h : Subst.apply ⟦t₁⟧ (get ⟦s₁⟧ i) = Subst.apply ⟦t₂⟧ (get ⟦s₂⟧ i) by exact h
    suffices h : ⟦s₁⟧ = ⟦s₂⟧ ∧ ⟦t₁⟧ = ⟦t₂⟧ by rw [h.left, h.right]
    exact ⟨Quotient.sound h₁, Quotient.sound h₂⟩

/-- Now we can write `s t` for applying substitution `s` on term `t`. -/
instance : CoeFun (Subst σ) (fun _ => Expr σ → Expr σ) where
  coe := apply

end Subst

/-!
  Now define expressions *with* explicit substitutions and "metavariables".
-/

mutual
/-- Explicit substitutions using de Bruijn indices. -/
inductive ES (σ : Type) where
  | subst  : ES σ → SE σ →     ES σ -- Substitution application.
  | zero   :                   ES σ -- Variable with de Bruijn index 0.
  | binder : ES σ →            ES σ -- Binder presence.
  | node   : σ → List (ES σ) → ES σ -- Tree node.
  | mvar   : Nat →             ES σ -- Expression "metavariable".

/-- Substition expressions using de Bruijn indices. -/
inductive SE (σ : Type) where
  | shift :               SE σ -- Shift overflow variables up by 1.
  | cons  : ES σ → SE σ → SE σ -- Prepend to sequence.
  | comp  : SE σ → SE σ → SE σ -- Chaining (composition) of substitutions.
  | mvar  : Nat →         SE σ -- Substitution "metavariable".
end

/-- Variable with arbitrary de Bruijn index. -/
def ES.var (σ) : Nat → ES σ
  | 0     => zero
  | i + 1 => subst (ES.var σ i) .shift

/-- The identity substitution. -/
def SE.id (σ) : SE σ :=
  cons .zero shift

/-- Metavariable assignment. -/
structure Assignment (σ : Type) where
  es : Nat → Expr σ
  se : Nat → Subst' σ

mutual
/-- Assign metavariables. -/
def ES.assign : Assignment σ → ES σ → Expr σ
  | a, .subst e s => Subst'.apply (SE.assign a s) (ES.assign a e)
  | _, .zero      => .var 0
  | a, .binder e  => .binder (ES.assign a e)
  | a, .node n es => .node n (nested a es)
  | a, .mvar i    => a.es i
where nested : Assignment σ → List (ES σ) → List (Expr σ)
  | _, []         => []
  | a, e :: es    => ES.assign a e :: nested a es

/-- Assign metavariables. -/
def SE.assign : Assignment σ → SE σ → Subst' σ
  | _, .shift     => .shift 1
  | a, .cons h t  => .cons (ES.assign a h) (SE.assign a t)
  | a, .comp s t  => .comp (SE.assign a s) (SE.assign a t)
  | a, .mvar i    => a.se i
end

end Leansubst
