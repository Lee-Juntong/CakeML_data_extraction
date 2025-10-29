-- LEAN 4 file for theorem: nsAll2_nsBind
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsAll2_nsBind : nsAll2_nsBind {VarName Value Env BinderType : Type}
  (binder_short : VarName → BinderType)
  (R : BinderType → Value → Value → Prop)
  (nsAll2 : (BinderType → Value → Value → Prop) → Env → Env → Prop)
  (nsBind : VarName → Value → Env → Env) :
  ∀ (x : VarName) (v1 v2 : Value) (e1 e2 : Env),
    R (binder_short x) v1 v2 ∧ nsAll2 R e1 e2 → nsAll2 R (nsBind x v1 e1) (nsBind x v2 e2) := by
  aesop
