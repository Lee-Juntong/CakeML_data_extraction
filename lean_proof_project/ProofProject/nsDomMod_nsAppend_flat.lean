-- LEAN 4 file for theorem: nsDomMod_nsAppend_flat
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsDomMod_nsAppend_flat : ∀ {N T : Type} (n1 n2 : N), nsDomMod n1 = Set.singleton ([] : List T) → nsDomMod (nsAppend n1 n2) = nsDomMod n2 := by
  aesop
