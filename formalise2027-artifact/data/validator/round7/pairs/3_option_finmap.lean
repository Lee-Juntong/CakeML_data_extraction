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
-- Finite maps
-- Represented concretely as a partial function `α → Option β`.
-- HOL4's `('a, 'b) fmap` is set-theoretically a partial function with
-- finite support; in this development the finiteness side condition is
-- not required by any client, so we model the API using the underlying
-- partial function directly.
-- ============================================================

/- HOL4: ('a, 'b) fmap -/
def Finmap (α : Type) (β : Type) : Type := α → Option β

namespace Finmap

/- HOL4: FEMPTY -/
def FEMPTY {α β : Type} : Finmap α β := fun _ => none

/- HOL4: FLOOKUP -/
def FLOOKUP {α β : Type} (m : Finmap α β) (k : α) : Option β := m k

/- HOL4: FUPDATE — point update at key `kv.1`. Requires `BEq α` so the
   update is computable. -/
def FUPDATE {α β : Type} [BEq α] (m : Finmap α β) (kv : α × β) : Finmap α β :=
  fun x => if x == kv.1 then some kv.2 else m x

/- HOL4: FDOM -/
def FDOM {α β : Type} (m : Finmap α β) : Set α := fun a => (m a).isSome

/- HOL4: FRANGE -/
def FRANGE {α β : Type} (m : Finmap α β) : Set β := fun b => ∃ a, m a = some b

/- HOL4: FEVERY -/
def FEVERY {α β : Type} (P : α × β → Prop) (m : Finmap α β) : Prop :=
  ∀ k val_, m k = some val_ → P (k, val_)

/- HOL4: FUPDATE_LIST -/
def FUPDATE_LIST {α β : Type} [BEq α] (m : Finmap α β) (l : List (α × β)) : Finmap α β :=
  l.foldl FUPDATE m

/- HOL4: o_f (map over values) -/
def o_f {α β γ : Type} (f : β → γ) (m : Finmap α β) : Finmap α γ :=
  fun x => (m x).map f

/- HOL4: alist_to_fmap — earliest binding wins. -/
def alist_to_fmap {α β : Type} [BEq α] (l : List (α × β)) : Finmap α β :=
  fun k => (l.find? (fun p => k == p.1)).map Prod.snd

/- HOL4: SUBMAP -/
def SUBMAP {α β : Type} (m1 m2 : Finmap α β) : Prop :=
  ∀ k val_, m1 k = some val_ → m2 k = some val_

/- HOL4: FUNION (left-biased union) -/
def FUNION {α β : Type} (m1 m2 : Finmap α β) : Finmap α β :=
  fun x => match m1 x with
    | some v => some v
    | none => m2 x

end Finmap

