import LeanTypeSound.Misc
/-! Round 2 check: the frozen statements of `tlookup_bij_suff` and `tlookup_bij_iff` (as in de795c9f6,
    without the `Nodup` hypothesis that Direct added) are false. The definitions of `tlookup`,
    `Sptree.lookup`, `Sptree.toList`, `Sptree.domain` and `BIJ` are unchanged from de795c9f6. -/
open HOL4

/-- Frozen `tlookup_bij_suff` is false: values {1,0} equal the domain {0,1}, but 0 and 1 both map to 1. -/
theorem not_tlookup_bij_suff :
    ¬ (∀ names : Sptree Nat, (fun x => x ∈ Sptree.toList names) = Sptree.domain names →
        BIJ (tlookup names) Set.univ Set.univ) := by
  intro h
  have hdom : (fun x => x ∈ Sptree.toList ([(0, 1), (1, 1), (1, 0)] : Sptree Nat)) =
      Sptree.domain ([(0, 1), (1, 1), (1, 0)] : Sptree Nat) := by
    funext x
    apply propext
    match x with
    | 0 => simp [Sptree.toList, Sptree.domain, Sptree.lookup, List.find?]
    | 1 => simp [Sptree.toList, Sptree.domain, Sptree.lookup, List.find?]
    | n + 2 => simp [Sptree.toList, Sptree.domain, Sptree.lookup, List.find?]
  obtain ⟨-, hinj, -⟩ := h _ hdom
  have := hinj 0 1 trivial trivial (by decide)
  exact absurd this (by decide)

/-- Frozen `tlookup_bij_iff` is false (left to right): `tlookup [(0,0),(0,5)]` is the identity,
    but the values {0,5} differ from the domain {0}. -/
theorem not_tlookup_bij_iff :
    ¬ (∀ names : Sptree Nat, BIJ (tlookup names) Set.univ Set.univ ↔
        (fun x => x ∈ Sptree.toList names) = Sptree.domain names) := by
  intro h
  have hid : ∀ k, tlookup ([(0, 0), (0, 5)] : Sptree Nat) k = k := by
    intro k
    by_cases hk : k = 0
    · subst hk; decide
    · simp [tlookup, Sptree.lookup, List.find?, Ne.symm hk]
  have hbij : BIJ (tlookup ([(0, 0), (0, 5)] : Sptree Nat)) Set.univ Set.univ :=
    ⟨fun _ _ => trivial, fun a1 a2 _ _ he => by rwa [hid, hid] at he, fun b _ => ⟨b, trivial, hid b⟩⟩
  have := congrFun ((h _).1 hbij) 5
  simp [Sptree.toList, Sptree.domain, Sptree.lookup, List.find?] at this

#print axioms not_tlookup_bij_suff
#print axioms not_tlookup_bij_iff
