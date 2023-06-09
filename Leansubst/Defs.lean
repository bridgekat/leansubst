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
def Subst (σ : Type) : Type :=
  Nat → Expr σ

namespace Subst

/-- The identity substitution. -/
def id (σ) : Subst σ :=
  fun i => .var i

/-- Shift overflow variables up. -/
def shift (σ) : Nat → Subst σ :=
  fun n i => .var (i + n)

/-- Prepend to sequence. -/
def cons : Expr σ → Subst σ → Subst σ :=
  fun e f => fun | 0 => e | i + 1 => f i

/-- Applies a renaming on a term. -/
def applyr : (Nat → Nat) → Expr σ → Expr σ
  | r, .var i     => .var (r i)
  | r, .binder e  => .binder (applyr (fun | 0 => 0 | i + 1 => r i + 1) e)
  | r, .node x es => .node x (nested r es)
where nested : (Nat → Nat) → List (Expr σ) → List (Expr σ)
  | _, []      => []
  | r, e :: es => applyr r e :: nested r es

/-- Composition of substitution and renaming. -/
def compr : Subst σ → (Nat → Nat) → Subst σ :=
  fun s r i => applyr r (s i)

/-- Applies a substitution on a term. -/
def apply : Subst σ → Expr σ → Expr σ
  | s, .var i     => s i
  | s, .binder e  => .binder (apply (cons (.var 0) (compr s (. + 1))) e)
  | s, .node n es => .node n (nested s es)
where nested : Subst σ → List (Expr σ) → List (Expr σ)
  | _, []      => []
  | s, e :: es => apply s e :: nested s es

/-- Composition of substitutions. -/
def comp : Subst σ → Subst σ → Subst σ :=
  fun s t i => apply t (s i)

/-- Composition of substitutions follows the expected definition. -/
theorem comp_def (s t : Subst σ) : comp s t = apply t ∘ s := rfl

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
  se : Nat → Subst σ

mutual
/-- Assign metavariables. -/
def ES.assign : Assignment σ → ES σ → Expr σ
  | a, .subst e s => Subst.apply (SE.assign a s) (ES.assign a e)
  | _, .zero      => .var 0
  | a, .binder e  => .binder (ES.assign a e)
  | a, .node n es => .node n (nested a es)
  | a, .mvar i    => a.es i
where nested : Assignment σ → List (ES σ) → List (Expr σ)
  | _, []         => []
  | a, e :: es    => ES.assign a e :: nested a es

/-- Assign metavariables. -/
def SE.assign : Assignment σ → SE σ → Subst σ
  | _, .shift     => Subst.shift _ 1
  | a, .cons h t  => Subst.cons (ES.assign a h) (SE.assign a t)
  | a, .comp s t  => Subst.comp (SE.assign a s) (SE.assign a t)
  | a, .mvar i    => a.se i
end

end Leansubst
