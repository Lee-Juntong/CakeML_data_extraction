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

/- HOL4: RTC (reflexive transitive closure) -/
inductive RTC {α : Type} (R : α → α → Prop) : α → α → Prop where
  | refl : ∀ (x : α), RTC R x x
  | step : ∀ (x y z : α), R x y → RTC R y z → RTC R x z

end HOL4

open HOL4
