-- LEAN 4 file for theorem: nsSub_conj
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsSub_conj : nsSub_conj {ι α : Type} (nsSub : (ι → α → α → Prop) → α → α → Prop) :
∀ (P Q : ι → α → α → Prop) (e1 e2 : α),
nsSub (λ id x y, P id x y ∧ Q id x y) e1 e2 ↔ nsSub P e1 e2 ∧ nsSub Q e1 e2 := by
  aesop
