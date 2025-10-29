-- LEAN 4 file for theorem: nsAll_alist_to_ns
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsAll_alist_to_ns : nsAll_alist_to_ns {β : Type u} (Short : String → String) (R : String → β → Prop) (alist_to_ns : List (String × β) → Std.Data.RBMap String β) (l : List (String × β)) : List.Forall (fun p => R (Short p.fst) p.snd) l → Std.Data.RBMap.all (alist_to_ns l) (fun k v => R k v) := by
  aesop
