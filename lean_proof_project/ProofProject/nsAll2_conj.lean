-- LEAN 4 file for theorem: nsAll2_conj
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsAll2_conj : ∀ (α β γ δ : Type) (P Q : α → β → γ → Prop) (e1 e2 : δ), nsAll2 (fun id x y => P id x y ∧ Q id x y) e1 e2 ↔ nsAll2 P e1 e2 ∧ nsAll2 Q e1 e2 := by
  aesop
