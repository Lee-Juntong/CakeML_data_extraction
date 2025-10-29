-- LEAN 4 file for theorem: nsLookup_nsAppend_none
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsLookup_nsAppend_none : ∀ (e1 : Env) (id : Ident) (e2 : Env),
  nsLookup (nsAppend e1 e2) id = none
  ↔
  (nsLookup e1 id = none ∧
   (nsLookup e2 id = none ∨
    ∃ (p1 : List ModSeg) (p2 : List ModSeg) (e3 : Val),
      p1 ≠ [] ∧ id_to_mods id = p1 ++ p2 ∧ nsLookupMod e1 p1 = some e3)) := by
  aesop
