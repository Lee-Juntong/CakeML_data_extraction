-- LEAN 4 file for theorem: nsLookup_FOLDR_nsLift
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsLookup_FOLDR_nsLift : universe u
variable (Env Prefix ShortId Name Value : Type u)
variable (nsLookup : Env → Name → Option Value)
variable (mk_id : Prefix → ShortId → Name)
variable (Short : ShortId → Name)
variable (nsLift : Env → Prefix → Env)
variable (FOLDR : (Env → Prefix → Env) → Env → Prefix → Env)

theorem nsLookup_FOLDR_nsLift : ∀ (e : Env) (p : Prefix) (k : ShortId),
  nsLookup (FOLDR nsLift e p) (mk_id p k) = nsLookup e (Short k) := by
  aesop
