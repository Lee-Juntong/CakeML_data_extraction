-- LEAN 4 file for theorem: nsSub_nsAppend_lift
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsSub_nsAppend_lift : ∀ (R : Id → Resource) (mn : ModuleName) (e1 e1' e2 e2' : Ns),
  nsSub (fun id => R (Long mn id)) e1 e1' ∧
  nsSub R e2 e2'
  →
  nsSub R (nsAppend (nsLift mn e1) e2) (nsAppend (nsLift mn e1') e2') := by
  aesop
