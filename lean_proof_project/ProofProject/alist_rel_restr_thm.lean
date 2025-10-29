-- LEAN 4 file for theorem: alist_rel_restr_thm
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem alist_rel_restr_thm : alist_rel_restr_thm {α β : Type u}
  (R : α → β → β → Prop) (e1 e2 : List (α × β)) (keys : List α) :
  alist_rel_restr R e1 e2 keys ↔
    ∀ (k : α), List.mem k keys → ∃ (v1 v2 : β),
      List.lookup k e1 = some v1 ∧ List.lookup k e2 = some v2 ∧ R k v1 v2 := by
  aesop
