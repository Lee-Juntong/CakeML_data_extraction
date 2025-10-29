-- LEAN 4 file for theorem: nsSub_mono2
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsSub_mono2 : nsSub_mono2 {α β : Type} (e1 e2 : α → Option β) (R1 R2 : α → β → β → Prop) :
  (∀ x y z, e1 x = some y ∧ e2 x = some z ∧ R1 x y z → R2 x y z) →
  ((∀ x y z, e1 x = some y ∧ e2 x = some z → R1 x y z) →
   (∀ x y z, e1 x = some y ∧ e2 x = some z → R2 x y z)) := by
  aesop
