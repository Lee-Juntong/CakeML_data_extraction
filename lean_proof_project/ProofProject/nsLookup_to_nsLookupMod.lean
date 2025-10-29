-- LEAN 4 file for theorem: nsLookup_to_nsLookupMod
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsLookup_to_nsLookupMod : nsLookup_to_nsLookupMod {N V T N_prime ModsV : Type} (nsLookup : N → V → Option T) (nsLookupMod : N → ModsV → Option N) (id_to_mods : V → ModsV) (id_to_n : V → N_prime) (Short : N_prime → V) : ∀ (n : N) (v : V) (t : T), nsLookup n v = some t → ∃ (m : N), nsLookupMod n (id_to_mods v) = some m ∧ nsLookup m (Short (id_to_n v)) = some t := by
  aesop
