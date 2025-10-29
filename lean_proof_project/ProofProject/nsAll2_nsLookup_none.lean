-- LEAN 4 file for theorem: nsAll2_nsLookup_none
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsAll2_nsLookup_none : ∀ {Namespace Name α : Type} {nsLookup : Namespace → Name → Option α} {nsAll2 : (α → α → Prop) → Namespace → Namespace → Prop}, ∀ (R : α → α → Prop) (e1 e2 : Namespace) (n : Name), nsAll2 R e1 e2 → (nsLookup e1 n = none ↔ nsLookup e2 n = none) := by
  aesop
