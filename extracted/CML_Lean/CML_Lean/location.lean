-- Auto-generated LEAN 4 file from HOL4 translation
-- Theory: location
-- Generated using Gemini API

namespace CML_Lean.location

/-
Original HOL4 Datatype: locn
locn = UNKNOWNpt | EOFpt | POSN num num
-/
inductive Locn where
  | UNKNOWNpt : Locn
  | EOFpt     : Locn
  | POSN      : Nat → Nat → Locn
  deriving Repr, DecidableEq

/-
Original HOL4 Definition: locnrow_def
locnrow (POSN r c) = r
-/
def locn_row (l : Locn) : Nat :=
  match l with
  | Locn.POSN r _ => r
  | _             => 0 -- Default value for UNKNOWNpt and EOFpt to ensure totality

/-
Original HOL4 Definition: locn_rowupdate_def
locn_rowupdate f (POSN r c) = POSN (f r) c
-/
def locn_row_update (f : Nat → Nat) (l : Locn) : Locn :=
  match l with
  | Locn.POSN r c => Locn.POSN (f r) c
  | other         => other

/-
Original HOL4 Definition: locncol_def
locncol (POSN r c) = c
-/
def locn_col (l : Locn) : Nat :=
  match l with
  | Locn.POSN _ c => c
  | _             => 0 -- Default value for UNKNOWNpt and EOFpt to ensure totality

/-
Original HOL4 Definition: locn_colupdate_def
locn_colupdate f (POSN r c) = POSN r (f c)
-/
def locn_col_update (f : Nat → Nat) (l : Locn) : Locn :=
  match l with
  | Locn.POSN r c => Locn.POSN r (f c)
  | other         => other

/-
Original HOL4 Datatype: locs
locs = Locs locn locn
-/
structure Locs where
  start  : Locn
  finish : Locn
  deriving Repr, DecidableEq

/-
Original HOL4 Definition: default_loc_def
default_loc = POSN 0 0
-/
def default_loc : Locn := Locn.POSN 0 0

/-
Original HOL4 Definition: start_locs_def
start_locs = Locs default_loc default_loc
-/
def start_locs : Locs := { start := default_loc, finish := default_loc }

/-
Original HOL4 Definition: unknown_loc_def
unknown_loc = Locs UNKNOWNpt UNKNOWNpt
-/
def unknown_loc : Locs := { start := Locn.UNKNOWNpt, finish := Locn.UNKNOWNpt }

/-
Original HOL4 Definition: locnle_def
locnle l1 l2 <=>
    l1 = l2 ∨ (* reflexivity, for free *)
    l1 = UNKNOWNpt ∨ (* minimal element *)
    l2 = EOFpt ∨ (* maximal element *)
    (* otherwise compare row and col lexicographically*)
    l2 ≠ UNKNOWNpt ∧ l1 ≠ EOFpt ∧
    (l1.row < l2.row ∨ l1.row = l2.row ∧ l1.col < l2.col)
-/
def locn_le (l1 l2 : Locn) : Prop :=
  l1 = l2 ∨
  l1 = Locn.UNKNOWNpt ∨
  l2 = Locn.EOFpt ∨
  (match l1, l2 with
  | Locn.POSN r1 c1, Locn.POSN r2 c2 =>
    (r1 < r2 ∨ (r1 = r2 ∧ c1 < c2))
  | _, _ => False)

/-
Original HOL4 Theorem: locnle_REFL
locnle l l
-/
theorem locn_le_refl (l : Locn) : locn_le l l := by
  simp [locn_le]


/-
Original HOL4 Theorem: locnle_total
locnle l1 l2 ∨ locnle l2 l1
-/
theorem locn_le_total (l1 l2 : Locn) : locn_le l1 l2 ∨ locn_le l2 l1 := by
  -- The proof for this theorem is omitted as per instructions (only the statement is requested).
  -- It would involve a thorough case analysis on the constructors of `Locn` and properties of natural numbers.
  sorry

/-
Original HOL4 Theorem: locnle_ANTISYM
locnle l1 l2 ∧ locnle l2 l1 ⇒ l1 = l2
-/
theorem locn_le_antisym (l1 l2 : Locn) : locn_le l1 l2 ∧ locn_le l2 l1 → l1 = l2 := by
  -- The proof for this theorem is omitted as per instructions (only the statement is requested).
  -- It would involve a thorough case analysis on the constructors of `Locn` and properties of natural numbers.
  sorry

/-
Original HOL4 Theorem: locnle_TRANS
locnle l1 l2 ∧ locnle l2 l3 ⇒ locnle l1 l3
-/
theorem locn_le_trans (l1 l2 l3 : Locn) : locn_le l1 l2 ∧ locn_le l2 l3 → locn_le l1 l3 := by
  -- The proof for this theorem is omitted as per instructions (only the statement is requested).
  -- It would involve a thorough case analysis on the constructors of `Locn` and properties of natural numbers.
  sorry

/-
Original HOL4 Theorem: locnle_end
locnle EOFpt l ⇔ l = EOFpt
-/
theorem locn_le_end (l : Locn) : locn_le Locn.EOFpt l ↔ l = Locn.EOFpt := by
  simp [locn_le]
  constructor
  . intro h
    cases h with
    | inl h => exact h
    | inr h =>
      cases h with
      | inl h => exact h.elim (Locn.EOFpt.noConfusion)
      | inr h =>
        cases h with
        | inl h => exact h
        | inr h => cases h.elim (Locn.EOFpt.noConfusion)
  . intro h
    left
    exact h := by sorry

/-
Original HOL4 Theorem: locnle_unknown
locnle l UNKNOWNpt ⇔ l = UNKNOWNpt
-/
theorem locn_le_unknown (l : Locn) : locn_le l Locn.UNKNOWNpt ↔ l = Locn.UNKNOWNpt := by
  simp [locn_le]
  constructor
  . intro h
    cases h with
    | inl h => exact h
    | inr h =>
      cases h with
      | inl h => exact h
      | inr h =>
        cases h with
        | inl h => exact h.elim (Locn.UNKNOWNpt.noConfusion)
        | inr h => cases h.elim (Locn.UNKNOWNpt.noConfusion)
  . intro h
    right
    left
    exact h := by sorry

/-
Original HOL4 Definition: locsle_def
locsle (Locs l1 _) (Locs l2 _) ⇔ locnle l1 l2
-/
def locs_le (l_range1 l_range2 : Locs) : Prop :=
  locn_le l_range1.start l_range2.start

/-
Original HOL4 Theorem: locsle_REFL
locsle l l
-/
theorem locs_le_refl (l : Locs) : locs_le l l := by
  simp [locs_le, locn_le_refl] := by sorry

/-
Original HOL4 Theorem: locsle_total
locsle l1 l2 ∨ locsle l2 l1
-/
theorem locs_le_total (l1 l2 : Locs) : locs_le l1 l2 ∨ locs_le l2 l1 := by
  unfold locs_le
  apply locn_le_total := by sorry

/-
Original HOL4 Theorem: locsle_TRANS
locsle l1 l2 ∧ locsle l2 l3 ⇒ locsle l1 l3
-/
theorem locs_le_trans (l1 l2 l3 : Locs) : locs_le l1 l2 ∧ locs_le l2 l3 → locs_le l1 l3 := by
  unfold locs_le
  intro h
  apply locn_le_trans
  exact ⟨h.left, h.right⟩ := by sorry

/-
Original HOL4 Definition: merge_locs_def
merge_locs (Locs l1 l2) (Locs l3 l4) = Locs l1 l4
-/
def merge_locs (l_range1 l_range2 : Locs) : Locs :=
  { start := l_range1.start, finish := l_range2.finish }

/-
Original HOL4 Definition: merge_list_locs_def
(merge_list_locs [] = unknown_loc) /\
  (merge_list_locs (h :: []) = h) /\
  (merge_list_locs (h1 :: h2 :: []) = merge_locs h1 h2) /\
  (merge_list_locs (h1 :: h2 :: t) = merge_list_locs (h1 :: t))
-/
def merge_list_locs : List Locs → Locs
  | []             => unknown_loc
  | [h]            => h
  | [h1, h2]       => merge_locs h1 h2
  | h1 :: _ :: t   => merge_list_locs (h1 :: t)

/-
Original HOL4 Definition: map_loc_def
(map_loc [] _ = []) /\
  (map_loc (h :: t) n =
    (h, Locs (POSN 0 n) (POSN 0 n)) :: map_loc t (n+1))
-/
def map_loc (l : List α) (n : Nat) : List (α × Locs) :=
  match l with
  | []      => []
  | h :: t  => (h, { start := Locn.POSN 0 n, finish := Locn.POSN 0 n }) :: map_loc t (n + 1)

/-
Original HOL4 Theorem: merge_locs_assoc
(merge_locs (merge_locs l1 l2) l3 = merge_locs l1 l3) ∧
  (merge_locs l1 (merge_locs l2 l3) = merge_locs l1 l3)
-/
theorem merge_locs_assoc (l1 l2 l3 : Locs) :
  (merge_locs (merge_locs l1 l2) l3 = merge_locs l1 l3) ∧
  (merge_locs l1 (merge_locs l2 l3) = merge_locs l1 l3) := by
  simp [merge_locs] := by sorry

/-
Original HOL4 Theorem: merge_list_locs_2
∀h1 h2 t.
    merge_list_locs (h1 :: h2 :: t) = merge_list_locs (merge_locs h1 h2 :: t)
-/
theorem merge_list_locs_2 (h1 h2 : Locs) (t : List Locs) :
  merge_list_locs (h1 :: h2 :: t) = merge_list_locs (merge_locs h1 h2 :: t) := by
  -- The proof for this theorem is omitted as per instructions (only the statement is requested).
  -- It relies on case analysis on `t` and the `merge_locs_assoc` theorem.
  sorry := by sorry

/-
Original HOL4 Theorem: merge_list_locs_nested
∀h t1 t2. merge_list_locs (merge_list_locs (h::t1) :: t2) =
            merge_list_locs (h :: t1 ++ t2)
-/
theorem merge_list_locs_nested (h : Locs) (t1 t2 : List Locs) :
  merge_list_locs (merge_list_locs (h :: t1) :: t2) =
  merge_list_locs (h :: t1 ++ t2) := by
  -- The proof for this theorem is omitted as per instructions (only the statement is requested).
  -- This is a more complex theorem requiring induction and careful application of the `merge_list_locs` definition and `merge_locs_assoc`.
  sorry := by sorry

/-
Original HOL4 Theorem: merge_list_locs_sing
merge_list_locs [h] = h
-/
theorem merge_list_locs_sing (h : Locs) : merge_list_locs [h] = h := by
  simp [merge_list_locs] := by sorry

/-
Original HOL4 Theorem: merge_locs_idem
merge_locs l l = l
-/
theorem merge_locs_idem (l : Locs) : merge_locs l l = l := by
  simp [merge_locs] := by sorry

end CML_Lean.location
