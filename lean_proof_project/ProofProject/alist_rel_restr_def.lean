-- LEAN 4 file for theorem: alist_rel_restr_def
-- Original HOL4 Definition

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem alist_rel_restr_def : inductive alist_rel_restr {K V : Type} (R : K → V → V → Prop) (l1 l2 : List (K × V)) : List K → Prop where
  | nil : alist_rel_restr R l1 l2 []
  | cons {k : K} {keys : List K} :
      ∀ (v1 v2 : V),
        (List.lookup k l1 = some v1) →
        (List.lookup k l2 = some v2) →
        R k v1 v2 →
        alist_rel_restr R l1 l2 keys →
        alist_rel_restr R l1 l2 (k :: keys) := by
  aesop
