-- LEAN 4 file for theorem: nsLookup_FOLDR_nsLift_some
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsLookup_FOLDR_nsLift_some : ∀ (e : Env) (p : List PathSegment) (id : Identifier) (v : Value), nsLookup (FOLDR nsLift e p) id = some v ↔ (p = [] ∧ nsLookup e id = some v) ∨ (p ≠ [] ∧ ∃ (p2 : List PathSegment) (n : NamePart), id = mk_id (p ++ p2) n ∧ nsLookup e (mk_id p2 n) = some v) := by
  aesop
