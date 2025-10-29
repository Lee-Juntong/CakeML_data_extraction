-- LEAN 4 file for theorem: nsDom_nsAppend_equal
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsDom_nsAppend_equal : ∀ {α β γ : Type} [BEq β] [BEq γ] (nsDom : α → β) (nsDomMod : α → γ) (nsAppend : α → α → α), ∀ (n1 n2 n3 n4 : α), (nsDom n1 = nsDom n3 ∧ nsDom n2 = nsDom n4 ∧ nsDomMod n1 = nsDomMod n3 ∧ nsDomMod n2 = nsDomMod n4) → (nsDom (nsAppend n1 n2) = nsDom (nsAppend n3 n4) ∧ nsDomMod (nsAppend n1 n2) = nsDomMod (nsAppend n3 n4)) := by
  aesop
