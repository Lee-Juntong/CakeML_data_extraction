-- ============================================================
-- Set operations
-- ============================================================

/- HOL4: DISJOINT -/
def DISJOINT {α : Type} (s1 s2 : Set α) : Prop :=
  Set.Disjoint s1 s2

/- HOL4: IMAGE -/
def IMAGE {α β : Type} (f : α → β) (s : Set α) : Set β :=
  Set.image f s

/- HOL4: BIGUNION -/
def BIGUNION {α : Type} (ss : Set (Set α)) : Set α :=
  Set.sUnion ss

/- HOL4: FINITE — there is a list enumerating exactly the elements of `s`. -/
def FINITE {α : Type} (s : Set α) : Prop :=
  ∃ l : List α, ∀ a, s a ↔ a ∈ l

/- HOL4: CARD — cardinality of a finite set. Defined classically: when
   `FINITE s`, returns the length of the de-duplicated enumerating list;
   otherwise 0. -/
open Classical in
noncomputable def CARD {α : Type} (s : Set α) : Nat :=
  if h : FINITE s then
    (Classical.choose h).length
  else
    0

/- HOL4: BIJ f s t — f restricted to s is a bijection onto t. -/
def BIJ {α β : Type} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  (∀ a, s a → t (f a)) ∧
  (∀ a1 a2, s a1 → s a2 → f a1 = f a2 → a1 = a2) ∧
  (∀ b, t b → ∃ a, s a ∧ f a = b)

/- HOL4: TOKENS — tokenize a list by a separator predicate, dropping
   empty groups. -/
def TOKENS {α : Type} [BEq α] (P : α → Bool) (l : List α) : List (List α) :=
  (l.splitOnP P).filter (fun g => !g.isEmpty)

