-- LEAN 4 file for theorem: nsLookup_nsAppend_some
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsLookup_nsAppend_some : ∀ (e1 : Env) (id : Id) (e2 : Env) (v : Val), nsLookup (nsAppend e1 e2) id = some v ↔ (nsLookup e1 id = some v ∨ (nsLookup e1 id = none ∧ nsLookup e2 id = some v ∧ (∀ (p1 p2 : List ModPathPart), p1 ≠ [] ∧ id_to_mods id = p1 ++ p2 → nsLookupMod e1 p1 = none))) := by
  aesop
