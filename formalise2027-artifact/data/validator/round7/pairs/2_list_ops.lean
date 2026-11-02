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

/- HOL4: PERM - permutation relation. Translated as `List.Perm`. -/
def PERM {α : Type} [BEq α] (l1 l2 : List α) : Prop := List.Perm l1 l2

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

/- HOL4: IS_PREFIX l1 l2 means "l2 is a prefix of l1" (l2 ≼ l1) -/
def IS_PREFIX {α : Type} [BEq α] (l1 l2 : List α) : Bool :=
  l2.isPrefixOf l1

/- HOL4: oEL n l - optional element at index n -/
def oEL {α : Type} (n : Nat) (l : List α) : Option α :=
  l[n]?

