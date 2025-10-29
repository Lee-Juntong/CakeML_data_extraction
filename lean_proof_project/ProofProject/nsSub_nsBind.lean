-- LEAN 4 file for theorem: nsSub_nsBind
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsSub_nsBind : nsSub_nsBind {Name Value Expr ContextItem : Type}
  (Short : Name → ContextItem)
  (nsSub : (ContextItem → Value → Value → Prop) → Expr → Expr → Prop)
  (nsBind : Name → Value → Expr → Expr) :
  ∀ (R : ContextItem → Value → Value → Prop) (x : Name) (v1 v2 : Value) (e1 e2 : Expr),
    R (Short x) v1 v2 ∧ nsSub R e1 e2 → nsSub R (nsBind x v1 e1) (nsBind x v2 e2) := by
  aesop
