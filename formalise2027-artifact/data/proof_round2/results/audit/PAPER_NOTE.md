# Proof round 2: facts for the paper

Written by the round 2 check thread on 2026-10-12. Evidence files are in this folder.

## Two translation defects that the review missed, found by the Direct proof run

Both are in the repaired baseline `de795c9f6`. Aristotle found them during the Direct run. We confirmed both in Lean.

1. **`CARD` is underdetermined.** `HOL4Prelude.lean` defines `CARD s` as the length of `Classical.choose (h : FINITE s)`. `FINITE s` only requires *some* list that enumerates `s`, and that list can contain duplicates. So the frozen `CARD {0}` is the length of an unspecified list among `[0]`, `[0,0]`, and so on, and it is not provably 1. HOL4 `CARD` is the cardinality. Direct changed the condition to a duplicate-free enumeration. `Check_CARD.lean` proves that the new `CARD` equals the length of any duplicate-free enumeration (standard axioms only).
2. **`Sptree` allows shadowed keys.** `Sptree α` is an association list, so a key can occur twice and `lookup` sees only the first entry. HOL4 sptrees have no such entries. Thus the frozen `tlookup_bij_suff` and `tlookup_bij_iff` are false. `Refute_tlookup_bij.lean` refutes both. The counterexamples are `[(0,1),(1,1),(1,0)]` and `[(0,0),(0,5)]`. The first proof uses `propext`, `Classical.choice`, and `Quot.sound`. The second uses only `propext`. Direct added the hypothesis that the keys are distinct (`Nodup`), which restores the HOL4 meaning.

Suggested place: one or two sentences where the paper discusses translation repairs during proving (the same kind as the `LawfulBEq` and `strsub` findings). The defect count changes from six to eight, or these two are reported as "found after the freeze by the prover".

## Round 2 counts (269 canonical theorems of de795c9f6)

Same measures as the proof table. Script: `table_r2.py`. Output: `table_out.txt`.

| Workflow | Local | Mod. | Aud. | Unch. | S.ed. | D.ed. |
|---|---|---|---|---|---|---|
| Skills | 59 | 59 | 51 | 59 | 0 | 0 |
| Docs | 63 | 63 | 57 | 63 | 0 | 0 |
| Second pass | 132 | 132 | 132 | 132 | 0 | 9 |
| Hybrid | 71 | 71 | 71 | 71 | 0 | 6 |
| Direct | 269 | 269 | 269 | 267 | 2 | 21 |

- Direct local proofs after each Aristotle task: 93, 229, 262, 266, 269 (5 tasks, about 4.5 hours, 4 "continue" messages). May had 1 continuation. Stage 2 (229) is the like-for-like point.
- Direct proves `decs_type_sound` and `semantics_type_sound`. Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- All definition edits in Direct, Second pass, and Hybrid only add termination proofs (`List.attach`, named `match`, `decreasing_by`). The exception is the `CARD` repair above.
- Deviations from May: the Aristotle MCP server was visible (but not called) in Skills, Second pass, and Docs. Hybrid made no Aristotle call. Hybrid and Direct used Lean 4.28.0. Claude Code is 2.1.287 and the model is Opus 4.7, effort xhigh.

## Git

- `lean-translate` now points to `de795c9f6`, so its history leads to the repaired translation.
- The method branches hold the round 2 results: `Lean-Skills-Official` (Skills), `lean4skills(prove)-docAccess` (Docs), `skills(prove)-docAccess-2pass` (Second pass), `CC-aristotle` (Hybrid), `direct-aristotle` (Direct).
- On 2026-10-12, at Juntong's request, the two repair commits were rewritten with Juntong as author and without Claude trailers. The trees are identical. `405848cad` is now `6ed1fdb58`, and `4841f993e` is now `de795c9f6`. Every round 2 branch was moved onto `de795c9f6`. The paper must cite the new hashes.
- The May heads are kept as tags `may2026/<branch>`. The commits that the paper cites (`aef82615e`, `0d1173557`, `88927cb6f`, `9f5188d63`, `41c815090`) are still reachable on GitHub through these tags.
