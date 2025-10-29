-- LEAN 4 file for theorem: nsSub_compute_thm
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsSub_compute_thm : ∀ (α : Type) (R : α → α → Prop) (e1 e2 : α), nsSub R e1 e2 ↔ nsSub_compute ([] : List α) R e1 e2 := by
  aesop
