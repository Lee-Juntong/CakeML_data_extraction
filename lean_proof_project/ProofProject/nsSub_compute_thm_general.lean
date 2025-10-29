-- LEAN 4 file for theorem: nsSub_compute_thm_general
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsSub_compute_thm_general : ∀ {A B : Type} (p : List A) (R : B → B → Prop) (e1 e2 : B), nsSub R (List.foldr nsLift e1 (List.reverse p)) (List.foldr nsLift e2 (List.reverse p)) ↔ nsSub_compute p R e1 e2 := by
  aesop
