# HOL4 library evidence for the post hoc checks (Table VI of the paper)

All excerpts are from the HOL4 repository, https://github.com/HOL-Theorem-Prover/HOL,
branch `develop` at commit `99698b3cf170095de9e2e1c0ae22238fb04ec3ff` (3 October 2026).
The fixities and definitions below have not changed in the period of the study.
CakeML sources are in `snapshots/<commit>/lean_type_sound/hol4-ultramin/`.

## Finding 4: grouping of `FV (Letrec defs b)`

`src/pred_set/src/pred_setScript.sml`

```
val UNION_DEF = new_infixl_definition
     ("UNION_DEF", (“UNION s t = {x:'a | x IN s \/ x IN t}”),500);
val _ = unicode_version{ u = UChar.union, tmnm = "UNION"}
...
val DIFF_DEF = new_infixl_definition
    ("DIFF_DEF",
     (“DIFF s t = {x:'a | x IN s /\ ~ (x IN t)}”),500);
```

`unicode_version` gives `∪` the fixity of `UNION`. Both operators are left
associative at precedence 500, so the CakeML equation

```
FV (Letrec defs b) = FV_defs defs ∪ FV b DIFF set (MAP (Short o FST) defs)
```

(`semanticPrimitivesPropsScript.sml`, line 194) groups as `(FV_defs defs ∪ FV b) DIFF ...`.
In Lean core (`Init/Core.lean` of Lean 4.29.1), `∪` is `infixl:65` and `\` is `infix:70`,
so the Lean text needs the parentheses that the round 3 repair removed.

Lean, `SemanticPrimitivesProps.lean` line 121:
- `b01347d3e`: `| .Letrec defs b => (FV_defs defs ∪ FV b) \ (fun x => ...)`
- `af5ac084c` and `252eab2cf`: `| .Letrec defs b => FV_defs defs ∪ (FV b \ (fun x => ...))`

## Finding 3: `FUPDATE_LIST FEMPTY (REVERSE (ZIP (tvs', ts')))`

`src/finite_maps/finite_mapScript.sml`

```
Definition FUPDATE_LIST:
  FUPDATE_LIST = FOLDL FUPDATE
End
Overload "|++" = “FUPDATE_LIST”
```

`src/finite_maps/alistScript.sml`

```
Definition alist_to_fmap_def:
  alist_to_fmap s = FOLDR (\(k,v) f.f|+(k,v)) FEMPTY s
End
...
    (alist_to_fmap ((k,v)::t) = alist_to_fmap t |+ (k,v))
...
Theorem FUPDATE_LIST_EQ_APPEND_REVERSE:
 !ls fm. fm |++ ls = alist_to_fmap (REVERSE ls ++ fmap_to_alist fm)
```

With `fm = FEMPTY` and `ls = REVERSE l`, `FEMPTY |++ REVERSE l = alist_to_fmap l`,
in which the first binding of a key wins. The frozen Lean prelude defines
`alist_to_fmap l k = (l.find? (fun p => k == p.1)).map Prod.snd` (first binding wins), and
the round 3 repair writes `Finmap.alist_to_fmap (tvs'.zip ts').reverse`
(`TypeSoundInvariants.lean`, lines 168 and 171), so the last binding wins.
At `af5ac084c` the prelude `alist_to_fmap` was still `sorry`; the difference became
observable when the definition pass (`dbb89adda`) gave it a body.

## Findings 6 and 13: comparator of `sort`

`mllistScript.sml`: `sort = mergesort$mergesort_tail`.

`src/sort/mergesortScript.sml`

```
Definition merge_tail_def:
  ...
  (merge_tail negate R (x::l1) (y::l2) acc =
    if R x y <> negate then ...
Definition mergesort_tail_def:
  mergesort_tail R l = mergesortN_tail F R (LENGTH l) l
End
```

`R x y <> negate` with `negate : bool` makes `R : 'a -> 'a -> bool`. The round 3
repair (`af5ac084c`, `Mllist.lean`) uses `cmp : α → α → ordering`.

## Finding 12: `UPDATE_LIST`

`miscScript.sml`: `UPDATE_LIST = FOLDL (combin$C (UNCURRY UPDATE))`.

`src/list/src/listScript.sml`

```
Definition FOLDL:
  FOLDL (f:'b->'a->'b) e [] = e /\
  FOLDL f e (x::l) = FOLDL f (f e x) l
End
```

This is a left fold, as is the Lean `updates.foldl` in `Misc.lean`.

## Finding 2: `nsAll2`

`namespaceScript.sml`

```
Definition nsSub_def:
  nsSub r env1 env2 ⇔
     (∀id v1. nsLookup env1 id = SOME v1 ⇒ ∃v2. nsLookup env2 id = SOME v2 ∧ r id v1 v2) ∧
     ∀path. nsLookupMod env2 path = NONE ⇒ nsLookupMod env1 path = NONE
End
Definition nsAll2_def:
  nsAll2 r env1 env2 ⇔ nsSub r env1 env2 ∧ nsSub (λx y z. r x z y) env2 env1
End
```

The closure rules of `type_v` in `TypeSoundInvariants.lean` (frozen baseline, lines
186 to 193 and 205 to 211) expand `nsAll2` by hand into equal value domains and the
typing property, and omit the condition on module paths (`nsLookupMod`).

## Findings 5, 7, 8, 15

- 5: `SemanticPrimitives.lean` line 146: `abbrev store (α : Type) := List (store_v α)`,
  so `List (store_v v)` and `store v` are the same type. HOL4 `semanticPrimitivesScript.sml`:
  `Type store = “:('a store_v) list”`.
- 7 and 11: HOL4 `string` is `char list`. The HOL4 equations of `v_to_char_list`
  return `SOME ""` and `SOME (STRING c cs)`, which are character lists.
- 8 and 14: `namespaceScript.sml` defines `id = Short 'n | Long 'm id`, so the second
  argument of `Long` is a full identifier.
- 15: `af5ac084c`, `SemanticsMin.lean` line 53 reads
  `(evaluate_prog_with_clock st env k prog).2 = .Rerr (.Rabort .Rtype_error)`. The
  round 4 record quotes the line without `k`.

## Table II and Section VI-C: strings and equality

Strings. `src/string/stringScript.sml` defines the character type as the numbers
below 256 and strings as character lists:

```
   ∃n. (λn. n < 256) n                          (line 21, CHAR_EXISTS)
val CHAR_TYPE = new_type_definition("char", CHAR_EXISTS);
Type string[pp] = ``:char list``                (line 236)
```

`mlstringScript.sml` (package) wraps such a list and indexes it by position in the list:

```
Datatype:
  mlstring = strlit string
End
Definition strsub_def[simp]:
  strsub (strlit s) n = EL n s
End
```

The frozen Lean `strsub` used `String.get ⟨n⟩`, whose argument is a UTF-8 byte
position. The Lean string "éa" is the character list `[CHR 233; #"a"]`, and `CHR 233`
is a valid HOL4 character. HOL4 gives `strsub (strlit [CHR 233; #"a"]) 1 = #"a"` by
`EL`, while the frozen Lean definition reads byte 1, which lies inside the two-byte
encoding of é.
`Refute_explode_thm.lean` refutes the frozen `explode_thm`, and `Check_repairs.lean`
proves it for the repaired `strsub`, which indexes `s.toList`.

Equality. `src/finite_maps/alistScript.sml` looks keys up with HOL equality:

```
Definition ALOOKUP_def[simp]:
  (ALOOKUP [] q = NONE) /\
  (ALOOKUP ((x,y)::t) q = if x = q then SOME y else ALOOKUP t q)
End
```

`namespaceScript.sml` defines `nsLookup` through `ALOOKUP`, and
`namespacePropsScript.sml` proves

```
Theorem nsLookup_nsBind[simp]:
   (!n v e. nsLookup (nsBind n v e) (Short n) = SOME v) ∧
   (!n n' v e. n ≠ Short n' ⇒ nsLookup (nsBind n' v e) n = nsLookup e n)
```

HOL equality is lawful at every type. The frozen Lean statement quantifies over any
`BEq` instance on the keys, and `Refute_nsLookup_nsBind.lean` refutes it with an
instance under which no key equals itself. With `LawfulBEq` added, `Check_repairs.lean`
proves it. HOL4 equality on runtime values is structural, while the frozen Lean
instances on `v` and `sem_env` were `fun _ _ => sorry`.
