-- LEAN 4 file for theorem: nsLookup_nsLift
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsLookup_nsLift : ∀ (NamePart : Type) (Env : Type) (α : Type) [DecidableEq NamePart] (Id : Type → Type) (nsLookup : Env → Id NamePart → Option α) (nsLift : NamePart → Env → Env), ∀ (mn : NamePart) (e : Env) (id : Id NamePart), nsLookup (nsLift mn e) id = match id with | Id.Long mn' id' => if mn = mn' then nsLookup e id' else none | Id.Short _ => none := by
  aesop
