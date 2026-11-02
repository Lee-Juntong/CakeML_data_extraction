-- ============================================================
-- Sptree (num-keyed maps)
-- HOL4's `'a spt` is a sparse patricia tree keyed by `num`; we represent
-- it concretely as a `List (Nat × α)` where the first matching key wins.
-- This loses the O(log n) characteristics but preserves the API
-- semantics needed by this development.
-- ============================================================

/- HOL4: 'a spt -/
def Sptree (α : Type) : Type := List (Nat × α)

namespace Sptree

/- HOL4: lookup -/
def lookup {α : Type} (k : Nat) (t : Sptree α) : Option α :=
  (t.find? (fun p => p.1 = k)).map Prod.snd

/- HOL4: insert -/
def insert {α : Type} (k : Nat) (v : α) (t : Sptree α) : Sptree α :=
  (k, v) :: t.filter (fun p => p.1 ≠ k)

/- HOL4: delete -/
def delete {α : Type} (k : Nat) (t : Sptree α) : Sptree α :=
  t.filter (fun p => p.1 ≠ k)

/- HOL4: fromAList -/
def fromAList {α : Type} (l : List (Nat × α)) : Sptree α := l

/- HOL4: domain -/
def domain {α : Type} (t : Sptree α) : Set Nat := fun n => (lookup n t).isSome

/- HOL4: toList (returns values only) -/
def toList {α : Type} (t : Sptree α) : List α := t.map Prod.snd

/- HOL4: toAList (returns key-value pairs) -/
def toAList {α : Type} (t : Sptree α) : List (Nat × α) := t

end Sptree

-- ============================================================
-- LazyList (potentially infinite lists)
-- HOL4's `'a llist` is a coinductive lazy list; we represent it as a
-- partial indexing function `Nat → Option α`, where a `none` at position
-- `n` indicates the list has ended by index `n`. (The intended invariant
-- is that `none` is downward-closed; this invariant is not enforced at
-- the type level but is preserved by `fromList`.)
-- ============================================================

/- HOL4: 'a llist -/
def LazyList (α : Type) : Type := Nat → Option α

namespace LazyList

open Classical

/- HOL4: LPREFIX l1 l2 — l1 is a prefix of l2. Every position present
   in l1 is present in l2 with the same value. -/
def LPREFIX {α : Type} (l1 l2 : LazyList α) : Prop :=
  ∀ n x, l1 n = some x → l2 n = some x

/- HOL4: fromList -/
def fromList {α : Type} (l : List α) : LazyList α := fun n => l[n]?

/- HOL4: toList — returns `some l` when the lazy list is finite (i.e.
   has a least index after which it is empty), otherwise `none`.
   Defined classically since the predicate is undecidable in general. -/
noncomputable def toList {α : Type} (ll : LazyList α) : Option (List α) :=
  if h : ∃ N, ∀ n, n ≥ N → ll n = none then
    let N := Classical.choose h
    some ((List.range N).filterMap ll)
  else
    none

end LazyList

