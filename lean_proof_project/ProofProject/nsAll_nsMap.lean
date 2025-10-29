-- LEAN 4 file for theorem: nsAll_nsMap
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsAll_nsMap : nsAll_nsMap {α β γ : Type} (f : β → γ) (n : NetStream (α × β)) (P : α → γ → Prop) : nsAll (fun x => P x.fst x.snd) (nsMap (fun y => (y.fst, f y.snd)) n) ↔ nsAll (fun x => P x.fst (f x.snd)) n := by
  aesop
