-- LEAN 4 file for theorem: mk_id_thm
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem mk_id_thm : mk_id_thm {IdType ModsType NType : Type} (mk_id : ModsType → NType → IdType) (id_to_mods : IdType → ModsType) (id_to_n : IdType → NType) : ∀ (id : IdType), mk_id (id_to_mods id) (id_to_n id) = id := by
  aesop
