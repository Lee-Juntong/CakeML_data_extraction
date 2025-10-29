-- LEAN 4 file for theorem: mk_id_surj
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem mk_id_surj : mk_id_surj {IdType PType NType : Type} (mk_id : PType → NType → IdType) : ∀ (id : IdType), ∃ (p : PType) (n : NType), id = mk_id p n := by
  aesop
