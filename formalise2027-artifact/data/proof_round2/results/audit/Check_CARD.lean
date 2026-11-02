import LeanTypeSound.Misc
/-! Round 2 check of the `CARD` edit in Direct.
    Frozen (de795c9f6):  CARD s = (Classical.choose (h : FINITE s)).length, where FINITE s only asks for SOME
    enumerating list, possibly with duplicates. The chosen list is unspecified, so the frozen CARD of {0}
    is the length of an unknown list among [0], [0,0], [0,0,0], ... and is not provably 1.
    Direct: CARD s = length of a chosen duplicate-free enumeration, which is the HOL4 cardinality. -/
open HOL4

-- Frozen `CARD`, copied from de795c9f6.
open Classical in
noncomputable def CARD_frozen {α : Type} (s : Set α) : Nat :=
  if h : FINITE s then (Classical.choose h).length else 0

/-- The frozen definition does not pin the value down: two enumerations of {0} of different lengths. -/
theorem frozen_FINITE_witness_not_unique :
    (∀ a : Nat, (fun x => x = 0) a ↔ a ∈ [0]) ∧ (∀ a : Nat, (fun x => x = 0) a ↔ a ∈ [0, 0]) ∧
    [0].length ≠ [0, 0].length := by
  refine ⟨fun a => by simp, fun a => by simp, by decide⟩

/-- The new definition gives the HOL4 value for every set with a duplicate-free enumeration. -/
theorem new_CARD_eq {α : Type} (s : Set α) (l : List α) (hl : l.Nodup) (hs : ∀ a, s a ↔ a ∈ l) :
    CARD s = l.length := CARD_eq_of_nodup hl hs

example : CARD (fun x : Nat => x = 0) = 1 := new_CARD_eq _ [0] (by simp) (fun a => by simp)

#print axioms new_CARD_eq
