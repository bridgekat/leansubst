import Leansubst.Basic

/-
-- Define a new tactic notation
syntax "tac" : tactic

macro_rules
  | `(tactic| tac) => `(tactic| assumption)

example (h : p) : p := by
  tac

-- You cannot prove the following theorem using `tac`
-- example (x : α) : x = x := by
--  tac

-- Let's extend `tac`. The tactic interpreter
-- tries all possible macro extensions for `tac` until one succeeds
macro_rules
  | `(tactic| tac) => `(tactic| rfl)

example (x : α) : x = x := by
  tac

example (x : α) (h : p) : x = x ∧ p := by
  apply And.intro <;> tac

-- We now add a (recursive) extension
macro_rules | `(tactic| tac) => `(tactic| apply And.intro <;> tac)

example (x : α) (h : p) : x = x ∧ p := by
  tac
-/
