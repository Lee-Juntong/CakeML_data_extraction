-- LEAN 4 file for theorem: nsAll_nsBind
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsAll_nsBind : ∀ (P : nsName → nsValue → Prop) (x : String) (v : nsValue) (e : List (nsName × nsValue)), P (nsName.short x) v ∧ nsAll P e → nsAll P (nsBind x v e) := by
  aesop
