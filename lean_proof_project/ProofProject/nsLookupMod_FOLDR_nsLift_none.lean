-- LEAN 4 file for theorem: nsLookupMod_FOLDR_nsLift_none
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsLookupMod_FOLDR_nsLift_none : ∀ {Env Val : Type} (nsLift : String → Env → Env) (nsLookupMod : Env → List String → Option Val) (e : Env) (p1 p2 : List String), nsLookupMod (List.foldr nsLift e p1) p2 = none ↔ (List.IsPrefix p1 p2 ∨ List.IsPrefix p2 p1) → ∃ (p3 : List String), p2 = p1 ++ p3 ∧ nsLookupMod e p3 = none := by
  aesop
