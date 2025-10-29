-- LEAN 4 file for theorem: nsLookupMod_nsLift
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsLookupMod_nsLift : ∀ (mn : Name) (e : Env) (path : List Name), nsLookupMod (nsLift mn e) path = match path with | [] => some (nsLift mn e) | (mn' :: path') => if mn = mn' then nsLookupMod e path' else none := by
  aesop
