-- LEAN 4 file for theorem: nsSub_nsMap
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsSub_nsMap : nsSub_nsMap {α β γ : Type} {NStruct : Type → Type}
  (nsSub : {T : Type} → (α → T → T → Prop) → NStruct T → NStruct T → Prop)
  (nsMap : {T T' : Type} → (T → T') → NStruct T → NStruct T')
  (R : α → β → β → Prop) (f : γ → β) (n1 n2 : NStruct γ) :
  nsSub R (nsMap f n1) (nsMap f n2) ↔ nsSub (λ id x y => R id (f x) (f y)) n1 n2 := by
  aesop
