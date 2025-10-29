-- LEAN 4 file for theorem: nsLookup_Bind_v_some
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsLookup_Bind_v_some : nsLookup_Bind_v_some (v : NameMap) (k : Name) (x : Address) : nsLookup (NameService.bind v []) k = some x ↔ ∃ y : String, k = Name.short y ∧ ALOOKUP v y = some x := by
  aesop
