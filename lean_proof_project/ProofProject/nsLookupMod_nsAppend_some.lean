-- LEAN 4 file for theorem: nsLookupMod_nsAppend_some
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsLookupMod_nsAppend_some : open Std (RBMap)

abbrev Key := String

inductive Env where
  | mk : RBMap Key Env → Env
  deriving Repr, Inhabited

def nsLookupMod : Env → List Key → Option Env :=
  sorry

def nsAppend : Env → Env → Env :=
  sorry

theorem nsLookupMod_nsAppend_some (e1 e2 : Env) (path : List Key) (x : Env) :
  (nsLookupMod (nsAppend e1 e2) path = some x) ↔
  (path = [] ∧ x = nsAppend e1 e2) ∨
  (path ≠ [] ∧
   (nsLookupMod e1 path = some x ∨
    (nsLookupMod e2 path = some x ∧
     ∀ (p1 p2 : List Key), p1 ≠ [] ∧ path = p1 ++ p2 → nsLookupMod e1 p1 = none))) := by
  aesop
