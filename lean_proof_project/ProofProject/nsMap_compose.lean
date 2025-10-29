-- LEAN 4 file for theorem: nsMap_compose
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsMap_compose : ∀ {α β γ : Type} (g : α → β) (e : Env α) (f : β → γ), nsMap f (nsMap g e) = nsMap (f ∘ g) e := by
  aesop
