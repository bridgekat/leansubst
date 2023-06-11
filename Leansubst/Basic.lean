import Std.Data.Nat.Lemmas
import Leansubst.Defs

/-!
This file contains equational lemmas related to `Expr` and `Subst`.
-/

namespace Leansubst.Subst

variable {σ : Type}

variable (s t u : Subst σ)
variable (n m i j k : Nat) (x : σ)
variable (e : Expr σ) (es : List (Expr σ))

/-- Applying the identity renaming. -/
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

/-- Applying composition of renamings. -/
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

/-- A difficult lemma for proving the `apply_apply` below... -/
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

The primitive operations handled are `id`, `shift n`, `cons e s`, `up n s`, `comp s₁ s₂` `apply s e`
and function application `s n`, where `n` are natural numbers, `s` are substitutions and `e` are
expressions built from `var n`, `binder e` and `node _ [e]`.

In [[1]](https://academic.oup.com/logcom/article-abstract/6/6/799/965899) it was proved that a set of
twelve rewriting rules (so-called `σ'`-calculus in the paper) constitute a confluent and terminating rewriting
system:

- (Id, VrId)  `apply id e`                → `e`
- (VrCons)    `apply (cons e s) (var 0)`  → `e`
- (App)       `apply s (app e₁ e₂)`       → `app (apply s e₁) (apply s e₂)`
- (Abs)       `apply s (lam e)`           → `lam (apply (cons (var 0) (comp s (shift 1))) e)`
- (Clos)      `apply s₂ (apply s₁ e)`     → `apply (comp s₁ s₂) e`
- (IdL)       `comp id s`                 → `s`
- (IdR, ShId) `comp s id`                 → `s`
- (ShCons)    `comp (shift 1) (cons e s)` → `s`
- (Map)       `comp (cons e s₁) s₂`       → `cons (apply s₂ e) (comp s₁ s₂)`
- (Assoc)     `comp (comp s₁ s₂) s₃`      → `comp s₁ (comp s₂ s₃)`
- (VrSh)      `cons (var 0) (shift 1)`    → `id`
- (SCons)     `cons (apply s (var 0)) (comp (shift 1) s)` → `s`

These rules deal with `id`, `shift 1`, `cons e s`, `comp s₁ s₂`, `apply s e` where `n`, `s` are the same,
`e` are expressions built form `var 0`, `app e₁ e₂` and `lam e`. It was further proved in
[[2]](https://www.ps.uni-saarland.de/Publications/documents/SchaeferEtAl_2015_Completeness.pdf)
that these rules are also *complete* for such set of primitives (in the sense that there exists a "separating
assignment" for two any expressions with different normal forms).

> Remark: as a rewriting system, its termination is *surprisingly* difficult to establish. However this is still
> understandable: by breaking down a simple substitution operation into many pieces, we are making the termination
> proof strictly harder, since now we have to find some decreasing measure which orients *every* small step,
> instead of one which just decreases from the starting position to the final position.
> [[2]](https://www.ps.uni-saarland.de/Publications/documents/SchaeferEtAl_2015_Completeness.pdf)
> has suggested using a proper *algorithm* instead of *rewriting* to avoid such difficulty.

In this project I choose to normalise `upr`, `applyr`, `compr`, function application (*), `single` and `var n`
(to `apply (shift n) (var 0)`) first; the remaining extensions which need to be handled are
`shift n` and `up n s`. The handling has to be more-or-less heuristic:

- For `up n s`, the strategy is to merge repeated applications first, then rewrite `n` (a sum of natural numbers)
  using `[Nat.add_succ, Nat.succ_add]` so that all `succ`s are moved to the outermost, and then I can expand
  the definition of `up`.
- For `shift n`, again repeated `apply (shift n)` are merged first, then `n` is rewritten so that the `succ`s
  bubble out. Now we cannot naively expand `shift (succ n)`: sometimes we need `comp (shift 1) (shift n)`
  (VrSh, SCons), but sometimes we need `comp (shift n) (shift 1)` (ShCons). I preferred the first expansion, and
  used a generalised rule for ShCons.

(*) Expansion of function application must be done manually for now
    (`simp` will stack overflow, and `rw` errors with "pattern is a metavariable")...
-/

-- To prevent infinite loops.
def var0 (σ) : Expr σ := .var 0
def shift1 (σ) : Subst σ := shift σ 1

/-
@[simp high]
theorem eval_expand : s n = apply s (.var n) := by
  rw [apply]
-/

@[simp high]
theorem single_expand : single n e = up n (cons e (id σ)) := rfl

@[simp high]
theorem var_expand : .var n = apply (shift σ n) (var0 σ) := by
  rw [var0, apply, shift, Nat.zero_add]

/-- Normalise `shift 0` to `id`. -/
@[simp high]
theorem shift_zero : shift σ 0 = id σ := by
  apply funext; intros i
  rw [id, shift]; rfl

/-- Merge adjacent `shift` (we can then move `succ` out). -/
@[simp high]
theorem shift_comp_shift : comp (shift σ n) (shift σ m) = shift σ (n + m) := by
  apply funext; intros i; rw [shift, comp, shift, apply, shift, Nat.add_assoc]

/-- Expand `shift (n + 1)`. This will not cause infinite loop, but should have lower priority. -/
@[simp low]
theorem shift_succ : shift σ (n + 1) = comp (shift1 σ) (shift σ n) := by
  apply funext; intros i
  rw [comp, shift1, shift, shift, apply, shift, Nat.add_comm n 1, Nat.add_assoc]

/-- Expand `up 0` to nothing. -/
@[simp high]
theorem up_zero : (up 0 s) = s := rfl

/-- Merge adjacent `up` (we can then move `succ` out). -/
@[simp high]
theorem up_up : (up m (up n s)) = up (n + m) s := by
  induction m with
  | zero => rfl
  | succ m ih => rw [up, Nat.add_succ, up, ih]

/-- Expand `up (n + 1)`. This will not cause infinite loop, but should have lower priority. -/
@[simp low]
theorem up_succ : (up (n + 1) s) = cons (var0 σ) (comp (up n s) (shift1 σ)) := by
  rw [up, compr_def]; rfl

@[simp high]
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

@[simp high]
theorem cons_apply : apply (cons e s) (var0 σ) = e := rfl

@[simp high]
theorem apply_binder : apply s (.binder e) = .binder (apply (up 1 s) e) := by
  rw [apply]

@[simp high]
theorem apply_node : apply s (.node x es) = .node x (es.map (apply s)) := by
  induction es with
  | nil => rw [List.map, apply, apply.nested]
  | cons h t ih => rw [List.map, apply, apply.nested] at *; congr 2; injection ih

@[simp high]
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

@[simp high]
theorem id_comp : comp (id σ) s = s := by
  apply funext; intros i; rw [comp_def, Function.comp, id, apply]

@[simp high]
theorem comp_id : comp s (id σ) = s := by
  apply funext; intros i; rw [comp_def, Function.comp, id_apply]

@[simp high]
theorem shift_comp_cons : comp (shift1 σ) (cons e s) = s := by
  apply funext; intros i; rw [comp_def, Function.comp, shift1, shift, apply]; rfl

@[simp high]
theorem cons_comp : comp (cons e s) t = cons (apply t e) (comp s t) := by
  apply funext; intros i; rw [comp_def, Function.comp, comp_def]; cases i <;> rfl

@[simp high]
theorem comp_assoc : comp (comp s t) u = comp s (comp t u) := by
  apply funext; intros i; simp only [comp_def, Function.comp, apply_apply]

@[simp high]
theorem zero_cons_shift : cons (var0 σ) (shift1 σ) = id σ := by
  apply funext; intros i; cases i <;> rfl

@[simp high]
theorem apply_zero_cons_shift_comp : cons (apply s (var0 σ)) (comp (shift1 σ) s) = s := by
  apply funext; intros i; cases i <;> rfl

/-- Generalises `shift_comp_cons`. -/
@[simp]
theorem shift_succ_comp_cons : comp (shift1 σ) (comp (shift σ n) (cons e s)) = comp (shift σ n) s := by
  rw [← comp_assoc, shift1, shift_comp_shift, Nat.add_comm, ← shift_comp_shift, comp_assoc, ← shift1, shift_comp_cons]

/-
example : apply (cons e s) (.var 0) = e := by simp
example : apply (cons e s) (.var (i + 1)) = apply s (.var i) := by simp
example : cons (apply (shift σ n) (var0 σ)) (shift σ (n + 1)) = shift σ n := by simp
example : cons (apply (comp (shift σ n) s) (var0 σ)) (comp (shift σ (n + 1)) s) = comp (shift σ n) s := by simp
-/

end Leansubst.Subst
