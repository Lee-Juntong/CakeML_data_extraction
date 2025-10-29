-- LEAN 4 file for theorem: nsSub_nsAppend2
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsSub_nsAppend2 : ∀ (α β : Type) (nsSub : α → β → β → Prop) (nsAppend : β → β → β) (R : α) (e1 e2 e2' : β), (nsSub R e1 e1 ∧ nsSub R e2 e2') → nsSub R (nsAppend e1 e2) (nsAppend e1 e2') := by
  aesop
