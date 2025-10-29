-- LEAN 4 file for theorem: nsLift_nsMap
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsLift_nsMap : nsLift_nsMap {α β M : Type} (f : α → β) (n : ns α) (mn : M) : nsLift mn (nsMap f n) = nsMap f (nsLift mn n) := by
  aesop
