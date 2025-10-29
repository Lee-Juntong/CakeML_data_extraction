-- LEAN 4 file for theorem: nsDom_nsLift
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsDom_nsLift : nsDom_nsLift {id S : Type}
  (nsDom : S → Set (List id))
  (nsLift : id → S → S)
  (Long : id → List id → List id) :
  ∀ (mn : id) (n : S), nsDom (nsLift mn n) = Set.image (Long mn) (nsDom n) := by
  aesop
