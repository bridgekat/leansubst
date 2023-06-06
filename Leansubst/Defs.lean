import Std.Data.Nat.Basic
import Std.Tactic.Basic

namespace Leansubst

/-! First we define expressions without explicit substitutions and "metavariables".
    They are also a semantic model for more complex expressions (so-called "de Bruijn algebra"). -/

/-- Abstract syntax tree using de Bruijn indices. -/
inductive Expr (σ : Type) where
  | var    : Nat →               Expr σ -- Variable in de Bruijn index.
  | binder : Expr σ →            Expr σ -- Binder presence.
  | node   : σ → List (Expr σ) → Expr σ -- Tree node.
-- Nested inductive types (e.g. the `List Expr` here) are a special case of mutual inductive types.

/-- Renamings. -/
inductive Renaming where
  | shift : Nat →            Renaming -- Shift overflow variables up.
  | cons  : Nat → Renaming → Renaming -- Prepend to sequence.

namespace Renaming

/-- The identity renaming. -/
def id : Renaming :=
  shift 0

/-- Evaluate renaming at a given index. -/
def get : Renaming → Nat → Nat
  | shift n,  i     => i + n
  | cons h _, 0     => h
  | cons _ t, i + 1 => get t i

/-- Composition of renamings. -/
def comp : Renaming → Renaming → Renaming
  | shift n,       shift m  => shift (n + m)
  | shift 0,       cons h t => cons h t
  | shift (n + 1), cons _ t => comp (shift n) t
  | cons h t,      r        => cons (r.get h) (comp t r)

/-- Applies a renaming on a term. -/
def apply {σ} : Renaming → Expr σ → Expr σ
  | r, .var i     => .var $ r.get i
  | r, .binder e  => .binder $ apply (cons 0 (comp r (shift 1))) e
  | r, .node n es => .node n $ applies r es
where applies {σ} : Renaming → List (Expr σ) → List (Expr σ)
  | _, []      => []
  | r, e :: es => apply r e :: applies r es
termination_by
  apply _ e    => sizeOf e
  applies _ es => sizeOf es

end Renaming

/-- Substitutions. -/
inductive Subst (σ : Type) where
  | shift : Nat →              Subst σ -- Shift overflow variables up.
  | cons  : Expr σ → Subst σ → Subst σ -- Prepend to sequence.

namespace Subst

def fromRenaming (σ) : Renaming → Subst σ
  | .shift n  => shift n
  | .cons h t => cons (.var h) (fromRenaming σ t)

instance {σ} : Coe Renaming (Subst σ) :=
  ⟨fromRenaming σ⟩

/-- The identity substitution. -/
def id (σ) : Subst σ :=
  shift 0

/-- Evaluate substitution at a given index. -/
def get {σ} : Subst σ → Nat → Expr σ
  | shift n,  i     => .var (i + n)
  | cons h _, 0     => h
  | cons _ t, i + 1 => get t i

/-- Composition of substitution and renaming. -/
def compr {σ} : Subst σ → Renaming → Subst σ
  | shift n,  r => Renaming.comp (.shift n) r
  | cons h t, r => cons (r.apply h) (compr t r)

/-- Applies a substitution on a term. -/
def apply {σ} : Subst σ → Expr σ → Expr σ
  | shift n,     .var i       => .var (i + n)
  | cons h _,    .var 0       => h
  | cons _ t,    .var (i + 1) => apply t (.var i)
  | s,           .binder e    => .binder (apply (cons (.var 0) (compr s (.shift 1))) e)
  | s,           .node n es   => .node n (applies s es)
where applies {σ} : Subst σ → List (Expr σ) → List (Expr σ)
  | _, []      => []
  | s, e :: es => apply s e :: applies s es
termination_by
  apply s e    => (sizeOf e, sizeOf s)
  applies s es => (sizeOf es, sizeOf s)

/-- Composition of substitutions. -/
def comp {σ} : Subst σ → Subst σ → Subst σ
  | shift n,       shift m  => shift (n + m)
  | shift 0,       cons h t => cons h t
  | shift (n + 1), cons _ t => comp (shift n) t
  | cons h t,      r        => cons (r.apply h) (comp t r)

end Subst

/-! Now define expressions **with** explicit substitutions and "metavariables". -/

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
def ES.assign {σ} : Assignment σ → ES σ → Expr σ
  | a, .subst e s => Subst.apply (SE.assign a s) (ES.assign a e)
  | _, .zero      => .var 0
  | a, .binder e  => .binder (ES.assign a e)
  | a, .node n es => .node n (ES.assigns a es)
  | a, .mvar i    => a.es i
where ES.assigns {σ} : Assignment σ → List (ES σ) → List (Expr σ)
  | _, []         => []
  | a, e :: es    => ES.assign a e :: ES.assigns a es

/-- Assign metavariables. -/
def SE.assign {σ} : Assignment σ → SE σ → Subst σ
  | _, .shift     => .shift 1
  | a, .cons h t  => .cons (ES.assign a h) (SE.assign a t)
  | a, .comp s t  => .comp (SE.assign a s) (SE.assign a t)
  | a, .mvar i    => a.se i
end

end Leansubst
