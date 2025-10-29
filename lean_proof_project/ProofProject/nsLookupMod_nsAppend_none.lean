-- LEAN 4 file for theorem: nsLookupMod_nsAppend_none
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsLookupMod_nsAppend_none : ∀ (e1 e2 : Env) (path : List Name), nsLookupMod (nsAppend e1 e2) path = none <-> (nsLookupMod e1 path = none ∧ (nsLookupMod e2 path = none ∨ (∃ (p1 p2 : List Name) (e3 : Env), p1 ≠ [] ∧ path = p1 ++ p2 ∧ nsLookupMod e1 p1 = some e3))) := by
  aesop
