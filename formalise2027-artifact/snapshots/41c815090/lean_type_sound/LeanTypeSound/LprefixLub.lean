/-
  Translation of lprefix_lubScript.sml
  Defines the least upper bound for lazy list prefixes.
-/
import LeanTypeSound.HOL4Prelude

open HOL4

/- HOL4:
Definition lprefix_lub_def:
  lprefix_lub ls lub ⇔
    (!ll. ll ∈ ls ⇒ LPREFIX ll lub) ∧
    (∀ub. (!ll. ll ∈ ls ⇒ LPREFIX ll ub) ⇒ LPREFIX lub ub)
End
-/
def lprefix_lub {α : Type} (ls : Set (LazyList α)) (lub : LazyList α) : Prop :=
  (∀ ll, ll ∈ ls → LazyList.LPREFIX ll lub) ∧
  (∀ ub, (∀ ll, ll ∈ ls → LazyList.LPREFIX ll ub) → LazyList.LPREFIX lub ub)
