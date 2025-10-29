-- LEAN 4 file for theorem: nsDom_nsAppend_flat
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsDom_nsAppend_flat : ∀ {α : Type} {Ns : Type} (nsDomMod : Ns → Set (List α)) (nsDom : Ns → Set (List α)) (nsAppend : Ns → Ns → Ns), ∀ (n1 n2 : Ns), nsDomMod n1 = {List.nil} → nsDom (nsAppend n1 n2) = nsDom n1 ∪ nsDom n2 := by
  aesop
