/-
  HOL4 Prelude - Library shim providing HOL4 primitives not in Lean stdlib.
  This module defines types and functions that serve as Lean counterparts
  for standard HOL4 library constructs.
-/

import Init.Data.List.Perm
import Batteries.Data.List.Basic

-- ============================================================
-- Set type (not in Lean 4 stdlib, normally from Mathlib)
-- ============================================================

def Set (α : Type) := α → Prop

namespace Set

instance {α : Type} : Membership α (Set α) := ⟨fun s a => s a⟩

def empty {α : Type} : Set α := fun _ => False
instance {α : Type} : EmptyCollection (Set α) := ⟨empty⟩

def univ {α : Type} : Set α := fun _ => True

def insert {α : Type} (a : α) (s : Set α) : Set α := fun x => x = a ∨ s x

def union {α : Type} (s1 s2 : Set α) : Set α := fun x => s1 x ∨ s2 x
instance {α : Type} : Union (Set α) := ⟨union⟩

def inter {α : Type} (s1 s2 : Set α) : Set α := fun x => s1 x ∧ s2 x
instance {α : Type} : Inter (Set α) := ⟨inter⟩

def sdiff {α : Type} (s1 s2 : Set α) : Set α := fun x => s1 x ∧ ¬s2 x
instance {α : Type} : SDiff (Set α) := ⟨sdiff⟩

def image {α β : Type} (f : α → β) (s : Set α) : Set β := fun b => ∃ a, s a ∧ f a = b

def sUnion {α : Type} (ss : Set (Set α)) : Set α := fun x => ∃ s, ss s ∧ s x

def Disjoint {α : Type} (s1 s2 : Set α) : Prop := ∀ x, ¬(s1 x ∧ s2 x)

def subset {α : Type} (s1 s2 : Set α) : Prop := ∀ x, s1 x → s2 x
instance {α : Type} : HasSubset (Set α) := ⟨subset⟩

end Set

-- Notation for set operations
notation:65 f " '' " s => Set.image f s
notation "⋃₀ " ss => Set.sUnion ss
notation "{" a "}" => Set.insert a Set.empty

namespace HOL4

