/-
  HOL4 Prelude - Library shim providing HOL4 primitives not in Lean stdlib.
  This module defines types and functions that serve as Lean counterparts
  for standard HOL4 library constructs.
-/

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

end Set

-- Notation for set operations
notation:65 f " '' " s => Set.image f s
notation "⋃₀ " ss => Set.sUnion ss
notation "{" a "}" => Set.insert a Set.empty

namespace HOL4

-- ============================================================
-- Basic list operations
-- ============================================================

/- HOL4: ALOOKUP -/
def ALOOKUP {α β : Type} [BEq α] : List (α × β) → α → Option β
  | [], _ => none
  | (k, v) :: rest, key => if k == key then some v else ALOOKUP rest key

/- HOL4: LUPDATE -/
def LUPDATE {α : Type} (x : α) (n : Nat) (l : List α) : List α :=
  l.set n x

/- HOL4: EL n l - element at index n -/
def EL {α : Type} [Inhabited α] (n : Nat) (l : List α) : α :=
  l[n]!

/- HOL4: TAKE -/
def TAKE {α : Type} (n : Nat) (l : List α) : List α :=
  l.take n

/- HOL4: DROP -/
def DROP {α : Type} (n : Nat) (l : List α) : List α :=
  l.drop n

/- HOL4: GENLIST f n -/
def GENLIST {α : Type} (f : Nat → α) (n : Nat) : List α :=
  (List.range n).map f

/- HOL4: ZIP -/
def ZIP {α β : Type} : List α × List β → List (α × β)
  | (l1, l2) => l1.zip l2

/- HOL4: UNZIP -/
def UNZIP {α β : Type} : List (α × β) → List α × List β
  | [] => ([], [])
  | (a, b) :: rest =>
    let (as_, bs) := UNZIP rest
    (a :: as_, b :: bs)

/- HOL4: EVERY -/
def EVERY {α : Type} (P : α → Bool) (l : List α) : Bool :=
  l.all P

/- HOL4: EXISTS -/
def EXISTS_ {α : Type} (P : α → Bool) (l : List α) : Bool :=
  l.any P

/- HOL4: ALL_DISTINCT -/
def ALL_DISTINCT {α : Type} [BEq α] : List α → Bool
  | [] => true
  | x :: xs => !(xs.any (· == x)) && ALL_DISTINCT xs

/- HOL4: LIST_REL -/
inductive LIST_REL {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : LIST_REL R [] []
  | cons : ∀ (x : α) (y : β) (xs : List α) (ys : List β),
    R x y → LIST_REL R xs ys → LIST_REL R (x :: xs) (y :: ys)

/- HOL4: PERM -/
def PERM {α : Type} [BEq α] (l1 l2 : List α) : Prop := sorry

/- HOL4: REPLICATE -/
def REPLICATE {α : Type} (n : Nat) (x : α) : List α :=
  List.replicate n x

/- HOL4: FLAT -/
def FLAT {α : Type} (l : List (List α)) : List α :=
  l.flatten

/- HOL4: MAP2 -/
def MAP2 {α β γ : Type} (f : α → β → γ) : List α → List β → List γ
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => f x y :: MAP2 f xs ys

/- HOL4: FILTER -/
def FILTER {α : Type} (P : α → Bool) (l : List α) : List α :=
  l.filter P

/- HOL4: nub (remove duplicates) -/
def nub {α : Type} [BEq α] : List α → List α
  | [] => []
  | x :: xs => if xs.any (· == x) then nub xs else x :: nub xs

/- HOL4: MEM -/
def MEM {α : Type} [BEq α] (x : α) (l : List α) : Bool :=
  l.any (· == x)

/- HOL4: SNOC -/
def SNOC {α : Type} (x : α) (l : List α) : List α :=
  l ++ [x]

/- HOL4: REVERSE -/
def REVERSE {α : Type} (l : List α) : List α :=
  l.reverse

/- HOL4: IS_PREFIX -/
def IS_PREFIX {α : Type} [BEq α] (l1 l2 : List α) : Bool :=
  l1.isPrefixOf l2

/- HOL4: oEL n l - optional element at index n -/
def oEL {α : Type} (n : Nat) (l : List α) : Option α :=
  l[n]?

-- ============================================================
-- Option operations
-- ============================================================

/- HOL4: OPT_MMAP -/
def OPT_MMAP {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | x :: xs => do
    let y ← f x
    let ys ← OPT_MMAP f xs
    return y :: ys

/- HOL4: IS_SOME -/
def IS_SOME {α : Type} : Option α → Bool
  | some _ => true
  | none => false

/- HOL4: IS_NONE -/
def IS_NONE {α : Type} : Option α → Bool
  | some _ => false
  | none => true

/- HOL4: THE -/
def THE {α : Type} [Inhabited α] : Option α → α
  | some x => x
  | none => default

-- ============================================================
-- Finite maps (opaque)
-- ============================================================

/- HOL4: ('a, 'b) fmap -/
opaque Finmap (α : Type) (β : Type) : Type := Unit

namespace Finmap

/- HOL4: FEMPTY -/
def FEMPTY {α β : Type} : Finmap α β := sorry

/- HOL4: FLOOKUP -/
def FLOOKUP {α β : Type} (m : Finmap α β) (k : α) : Option β := sorry

/- HOL4: FUPDATE -/
def FUPDATE {α β : Type} (m : Finmap α β) (kv : α × β) : Finmap α β := sorry

/- HOL4: FDOM -/
def FDOM {α β : Type} (m : Finmap α β) : Set α := sorry

/- HOL4: FRANGE -/
def FRANGE {α β : Type} (m : Finmap α β) : Set β := sorry

/- HOL4: FEVERY -/
def FEVERY {α β : Type} (P : α × β → Prop) (m : Finmap α β) : Prop := sorry

/- HOL4: FUPDATE_LIST -/
def FUPDATE_LIST {α β : Type} (m : Finmap α β) (l : List (α × β)) : Finmap α β := sorry

/- HOL4: o_f (map over values) -/
def o_f {α β γ : Type} (f : β → γ) (m : Finmap α β) : Finmap α γ := sorry

/- HOL4: alist_to_fmap -/
def alist_to_fmap {α β : Type} (l : List (α × β)) : Finmap α β := sorry

/- HOL4: SUBMAP -/
def SUBMAP {α β : Type} (m1 m2 : Finmap α β) : Prop := sorry

/- HOL4: FUNION -/
def FUNION {α β : Type} (m1 m2 : Finmap α β) : Finmap α β := sorry

end Finmap

-- ============================================================
-- Sptree (num-keyed maps, opaque)
-- ============================================================

/- HOL4: 'a spt -/
opaque Sptree (α : Type) : Type := Unit

namespace Sptree

/- HOL4: lookup -/
def lookup {α : Type} (k : Nat) (t : Sptree α) : Option α := sorry

/- HOL4: insert -/
def insert {α : Type} (k : Nat) (v : α) (t : Sptree α) : Sptree α := sorry

/- HOL4: delete -/
def delete {α : Type} (k : Nat) (t : Sptree α) : Sptree α := sorry

/- HOL4: fromAList -/
def fromAList {α : Type} (l : List (Nat × α)) : Sptree α := sorry

/- HOL4: domain -/
def domain {α : Type} (t : Sptree α) : Set Nat := sorry

/- HOL4: toList -/
def toList {α : Type} (t : Sptree α) : List (Nat × α) := sorry

end Sptree

-- ============================================================
-- LazyList (opaque)
-- ============================================================

/- HOL4: 'a llist -/
opaque LazyList (α : Type) : Type := Unit

namespace LazyList

/- HOL4: LPREFIX -/
def LPREFIX {α : Type} (l1 l2 : LazyList α) : Prop := sorry

/- HOL4: fromList -/
def fromList {α : Type} (l : List α) : LazyList α := sorry

/- HOL4: toList -/
def toList {α : Type} (ll : LazyList α) : Option (List α) := sorry

end LazyList

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

-- ============================================================
-- Word types (opaque stubs)
-- ============================================================

/- HOL4: word8 -/
abbrev word8 := UInt8

/- HOL4: word64 -/
abbrev word64 := UInt64

/- HOL4: word_add, word_sub, etc. for word8 -/
def word_add_8 (a b : word8) : word8 := a + b
def word_sub_8 (a b : word8) : word8 := a - b
def word_and_8 (a b : word8) : word8 := a &&& b
def word_or_8 (a b : word8) : word8 := a ||| b
def word_xor_8 (a b : word8) : word8 := a ^^^ b
def word_lsl_8 (a : word8) (n : Nat) : word8 := sorry
def word_lsr_8 (a : word8) (n : Nat) : word8 := sorry
def word_asr_8 (a : word8) (n : Nat) : word8 := sorry
def word_ror_8 (a : word8) (n : Nat) : word8 := sorry

/- HOL4: word_add, word_sub, etc. for word64 -/
def word_add_64 (a b : word64) : word64 := a + b
def word_sub_64 (a b : word64) : word64 := a - b
def word_and_64 (a b : word64) : word64 := a &&& b
def word_or_64 (a b : word64) : word64 := a ||| b
def word_xor_64 (a b : word64) : word64 := a ^^^ b
def word_lsl_64 (a : word64) (n : Nat) : word64 := sorry
def word_lsr_64 (a : word64) (n : Nat) : word64 := sorry
def word_asr_64 (a : word64) (n : Nat) : word64 := sorry
def word_ror_64 (a : word64) (n : Nat) : word64 := sorry

/- HOL4: w2n -/
def w2n_8 (w : word8) : Nat := w.toNat
def w2n_64 (w : word64) : Nat := w.toNat

/- HOL4: n2w -/
def n2w_8 (n : Nat) : word8 := n.toUInt8
def n2w_64 (n : Nat) : word64 := n.toUInt64

/- HOL4: i2w -/
def i2w_8 (i : Int) : word8 := sorry
def i2w_64 (i : Int) : word64 := sorry

-- ============================================================
-- IEEE754 floating point (opaque stubs)
-- ============================================================

/- HOL4: fp64_lessThan etc. -/
def fp64_lessThan (a b : word64) : Bool := sorry
def fp64_lessEqual (a b : word64) : Bool := sorry
def fp64_greaterThan (a b : word64) : Bool := sorry
def fp64_greaterEqual (a b : word64) : Bool := sorry
def fp64_equal (a b : word64) : Bool := sorry
def fp64_abs (a : word64) : word64 := sorry
def fp64_negate (a : word64) : word64 := sorry
def fp64_sqrt (_rm : Unit) (a : word64) : word64 := sorry
def fp64_add (_rm : Unit) (a b : word64) : word64 := sorry
def fp64_sub (_rm : Unit) (a b : word64) : word64 := sorry
def fp64_mul (_rm : Unit) (a b : word64) : word64 := sorry
def fp64_div (_rm : Unit) (a b : word64) : word64 := sorry
def fp64_mul_add (_rm : Unit) (a b c : word64) : word64 := sorry
def roundTiesToEven : Unit := ()

-- ============================================================
-- Comparison type
-- ============================================================

/- HOL4: ordering (LESS | EQUAL | GREATER) -/
inductive ordering where
  | LESS
  | EQUAL
  | GREATER
deriving Repr, BEq, Inhabited

-- ============================================================
-- Char operations
-- ============================================================

/- HOL4: ORD -/
def ORD (c : Char) : Nat := c.toNat

/- HOL4: CHR -/
def CHR (n : Nat) : Char := Char.ofNat n

-- ============================================================
-- FOLDR / FOLDL
-- ============================================================

/- HOL4: FOLDR -/
def FOLDR {α β : Type} (f : α → β → β) (b : β) (l : List α) : β :=
  l.foldr f b

/- HOL4: FOLDL -/
def FOLDL {α β : Type} (f : β → α → β) (b : β) (l : List α) : β :=
  l.foldl f b

end HOL4

open HOL4
