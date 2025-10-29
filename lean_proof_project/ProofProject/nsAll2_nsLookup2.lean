-- LEAN 4 file for theorem: nsAll2_nsLookup2
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsAll2_nsLookup2 : nsAll2_nsLookup2 {Name Value : Type} (nsAll2 : (Name → Value → Value → Prop) → (Name → Option Value) → (Name → Option Value) → Prop) : ∀ (R : Name → Value → Value → Prop) (e1 e2 : Name → Option Value) (n : Name) (v2 : Value), (e2 n = some v2 ∧ nsAll2 R e1 e2) → ∃ (v1 : Value), e1 n = some v1 ∧ R n v1 v2 := by
  aesop
