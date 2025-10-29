-- LEAN 4 file for theorem: nsAll2_nsBindList
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsAll2_nsBindList : ∀ {α : Type u} (R : String → Option α → Option α → Prop) (l1 l2 e1 e2 : List (String × Option α)), List.Forall₂ (λ (p1 : String × Option α) (p2 : String × Option α), p1.fst = p2.fst ∧ R p1.fst p1.snd p2.snd) l1 l2 ∧ nsAll2 R e1 e2 → nsAll2 R (nsBindList l1 e1) (nsBindList l2 e2) := by
  aesop
