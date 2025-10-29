-- LEAN 4 file for theorem: nsAll2_alist_to_ns
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsAll2_alist_to_ns : nsAll2_alist_to_ns {α : Type} (R : String → α → α → Prop) (l1 l2 : List (String × α)) :
  List.Rel (fun (p1 : String × α) (p2 : String × α) => p1.fst = p2.fst ∧ R (Short p1.fst) p1.snd p2.snd) l1 l2 →
  nsAll2 R (alist_to_ns l1) (alist_to_ns l2) := by
  aesop
