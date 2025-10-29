-- LEAN 4 file for theorem: alistSub_cong
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem alistSub_cong : ∀ {α : Type} (l1 l2 l1' l2' : List (Nat × α)) (R R' : Nat → α → α → Prop), l1 = l1' ∧ l2 = l2' ∧ (∀ (n : Nat) (x y : α), ALOOKUP l1' n = some x ∧ ALOOKUP l2' n = some y → R n x y ↔ R' n x y) → (alistSub R l1 l2 ↔ alistSub R' l1' l2') := by
  aesop
