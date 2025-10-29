-- LEAN 4 file for theorem: nsSub_refl
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsSub_refl : ∀ {α β δ : Type} (P : α → β → Prop) (R : α → β → β → Prop), (∀ (n : α) (x : β), P n x → R n x x) → (∀ (e : δ), nsAll P e → nsSub R e e) := by
  aesop
