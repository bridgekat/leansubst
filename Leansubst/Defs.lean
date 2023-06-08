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

/-- The identity substitution. -/
def id (σ) : Subst' σ :=
  shift 0

/-- Extract first element in sequence. -/
def head : Subst' σ → Expr σ
  | shift n  => .var n
  | cons h _ => h

/-- Drops first element in sequence. -/
def tail : Subst' σ → Subst' σ
  | shift n  => shift (n + 1)
  | cons _ t => t

/-- Drops first `n` elements in sequence. -/
def drop : Nat → Subst' σ → Subst' σ
  | 0,     s => s
  | n + 1, s => tail (drop n s)

/-- Get element at given index. -/
def get : Nat → Subst' σ → Expr σ :=
  fun n s => head (drop n s)

/-- Extensional equivalence of substitutions. -/
instance setoid (σ) : Setoid (Subst' σ) where
  r     := fun s t => ∀ i, s.get i = t.get i
  iseqv :=
  { refl  := fun _ _ => .refl _
    symm  := fun h i => .symm (h i)
    trans := fun h₁ h₂ i => .trans (h₁ i) (h₂ i) }

/-! Instructions for the `simp` tactic. -/
@[simp↓ high] theorem id_expand : id σ = shift 0 := rfl
@[simp low] theorem shift_zero : shift 0 = id σ := rfl
@[simp high] theorem head_shift (n) : @head σ (shift n) = .var n := rfl
@[simp high] theorem head_cons (h t) : @head σ (cons h t) = h := rfl
@[simp↓ high] theorem tail_expand (s) : @tail σ s = drop 1 s := rfl
@[simp low] theorem drop_one (s) : @drop σ 1 s = tail s := rfl

@[simp high] theorem drop_zero (s) : @drop σ 0 s = s := rfl

@[simp high]
theorem drop_drop (n m s) : @drop σ n (drop m s) = drop (m + n) s := by
  induction n with | zero => rfl | succ _ ih => rw [drop, ih, tail]; rfl

@[simp high]
theorem drop_shift (n m) : @drop σ n (shift m) = shift (m + n) := by
  induction n with | zero => rfl | succ _ ih => rw [drop, ih, tail]; rfl

@[simp high]
theorem drop_cons (n h t) : @drop σ (n + 1) (cons h t) = drop n t := by
  induction n with | zero => rfl | succ _ ih => rw [drop, ih, tail]; rfl

@[simp↓ high] theorem get_expand (n s) : @get σ n s = head (drop n s) := rfl
@[simp low] theorem head_drop (s n) : @head σ (drop n s) = get n s := rfl

/-- Shift variables with level ≥ `n` by `m` levels (ugly bootstrapping definition). -/
def applys : Nat → Nat → Expr σ → Expr σ
  | n, m, .var i     => if n <= i then .var (i + m) else .var i
  | n, m, .binder e  => .binder (applys (n + 1) m e)
  | n, m, .node x es => .node x (nested n m es)
where nested : Nat → Nat → List (Expr σ) → List (Expr σ)
  | _, _, []      => []
  | n, m, e :: es => applys n m e :: nested n m es

/-- Composition of substitution and shift (ugly bootstrapping definition). -/
def comps : Subst' σ → Nat → Subst' σ
  | shift n,  m => .shift (n + m)
  | cons h t, m => cons (applys 0 m h) (comps t m)

/-- Composition of substitution and shift follows the expected definition. -/
theorem comps_def (s : Subst' σ) (n : Nat) : ∀ i, get i (comps s n) = applys 0 n (get i s) := by
  intros i
  induction s generalizing i with
  | shift m =>  
    simp only [get, head, comps, drop_shift, applys, Nat.zero_le, ite_true]
    rw [Nat.add_assoc, Nat.add_comm n i, ← Nat.add_assoc] 
  | cons h s ih =>
    simp only [comps, get_expand] at *
    cases i with
    | zero => rfl
    | succ i => simp only [drop_cons] at *; rw [ih]

/-- Applies a substitution on a term. -/
def apply : Subst' σ → Expr σ → Expr σ
  | s, .var i     => get i s
  | s, .binder e  => .binder (apply (cons (.var 0) (comps s 1)) e)
  | s, .node n es => .node n (nested s es)
where nested : Subst' σ → List (Expr σ) → List (Expr σ)
  | _, []      => []
  | s, e :: es => apply s e :: nested s es
termination_by
  apply s e   => (sizeOf e, sizeOf s)
  nested s es => (sizeOf es, sizeOf s)

/-- Composition of substitutions. -/
def comp : Subst' σ → Subst' σ → Subst' σ
  | shift n,  r => drop n r
  | cons h t, r => cons (apply r h) (comp t r)

/-- Composition of substitutions follows the expected definition. -/
theorem comp_def (s t : Subst' σ) : ∀ i, get i (comp s t) = apply t (get i s) := by
  intros i
  induction s generalizing t i with
  | shift n => simp only [comp, get_expand, drop_drop, drop_shift, head_shift, apply]
  | cons h s ih =>
    simp only [comp, get_expand] at *
    cases i with
    | zero => rfl
    | succ i => simp only [drop_cons]; rw [ih]

/-- Now we can write `s t` for applying substitution `s` on term `t`. -/
instance : CoeFun (Subst' σ) (fun _ => Expr σ → Expr σ) where
  coe := apply

end Subst'

/-- Substitution modulo extensional equivalence. -/
def Subst (σ : Type) : Type :=
  Quotient (Subst'.setoid σ)

namespace Subst

local notation:arg "⟦" a "⟧" => Quotient.mk (Subst'.setoid _) a

/-- Lifted constructor `shift`. -/
def shift (σ) : Nat → Subst σ :=
  fun n => ⟦Subst'.shift n⟧

/-- Lifted constructor `cons`. -/
def cons : Expr σ → Subst σ → Subst σ :=
  fun e => Quotient.lift (fun s => ⟦Subst'.cons e s⟧) $ by
    intros s t h
    apply Quotient.sound; intros i
    cases i with
    | zero => rfl
    | succ i => simp only [Subst'.get_expand, Subst'.drop_cons]; exact h i

/-- Lifted constructor `id`. -/
def id (σ) : Subst σ :=
  ⟦Subst'.id σ⟧

/-- Evaluate substitution at a given index. -/
def get : Nat → Subst σ → Expr σ :=
  fun n => Quotient.lift (Subst'.get n) $
    fun _ _ h => h n

/-- Composition of substitution and shift. -/
def comps : Subst σ → Nat → Subst σ :=
  Quotient.lift (fun s n => ⟦Subst'.comps s n⟧) respects
where
  respects (s t : Subst' σ) (h : s ≈ t) : _ := by
    apply funext; intros n
    apply Quotient.sound; intros i
    rw [Subst'.comps_def, Subst'.comps_def, h i]

/-- Applies a substitution on a term. -/
def apply : Subst σ → Expr σ → Expr σ :=
  Quotient.lift Subst'.apply respects
where
  respects (s t : Subst' σ) (h : s ≈ t) : _ := by
    apply funext; intros e; revert s t
    -- Induction on `e`.
    let motive := fun (e : Expr σ) => ∀ (s t : Subst' σ), s ≈ t → s e = t e
    apply @Expr.recOn _ (fun e => motive e) (List.foldr (fun e etc => motive e ∧ etc) True)
      <;> intros <;> (try trivial) <;> intros s t h
    case var i => simp only [Subst'.apply, h i]
    case binder e' ih =>
      simp only [Subst'.apply]; congr 1
      apply ih
      apply Quotient.exact
      suffices h : cons (.var 0) (comps ⟦s⟧ 1) = cons (.var 0) (comps ⟦t⟧ 1) by exact h
      suffices h : ⟦s⟧ = ⟦t⟧ by rw [h]
      exact Quotient.sound h
    case node n es ih =>
      simp only [Subst'.apply, true_and]; congr 1
      induction es with
      | nil => simp only [Subst'.apply.nested]
      | cons h' t' ih' =>
        simp only [List.foldr] at ih
        simp only [Subst'.apply.nested]; congr 1
        exacts [ih.left _ _ h, ih' ih.right]

/-- Composition of substitutions. -/
def comp : Subst σ → Subst σ → Subst σ :=
  Quotient.lift₂ (fun s t => ⟦Subst'.comp s t⟧) respects
where
  respects (s₁ t₁ s₂ t₂ : Subst' σ) (h₁ : s₁ ≈ s₂) (h₂ : t₁ ≈ t₂) : _ := by
    apply Quotient.sound; intros i
    rw [Subst'.comp_def, Subst'.comp_def, h₁ i, apply.respects]; exact h₂

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
