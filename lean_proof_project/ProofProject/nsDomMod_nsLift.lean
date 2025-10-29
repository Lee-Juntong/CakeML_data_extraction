-- LEAN 4 file for theorem: nsDomMod_nsLift
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsDomMod_nsLift : nsDomMod_nsLift {K N : Type} (mn : K) (n : N) : nsDomMod (nsLift mn n) = Set.insert List.nil (Set.image (fun l => mn :: l) (nsDomMod n)) := by
  aesop
