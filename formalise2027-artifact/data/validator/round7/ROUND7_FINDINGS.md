# Round 7: prelude review (HOL4Prelude.lean at de795c9f6 against HOL4 library definitions)

## Setup
- Validator: Claude Haiku 5.5 run as a subagent. This replaces Gemini 3.8 Flash because the Gemini quota ran out. As a subagent it runs with no temperature setting.
- Prompt: the round 4/5 prompt, verbatim (validator_prompt.md).
- Calls: 3 runs × 8 section pairs = 24 calls. The prelude was split into 8 sections, and each section was paired with the HOL4 definitions of the constants it names.
- HOL4 source: branch develop of HOL-Theorem-Prover/HOL, fetched 2026-10-15T10:29:52Z. The commit sha is unknown. Each file's sha256 is recorded in pairs/INDEX.md.

## Raw outcome
- 9 calls answered RIGHT: sets in runs 1 and 2, list ops in all three runs, option/finmap in all three runs, and misc in run 1.
- The other 15 calls reported 27 error items (`errors` entries in the JSON answers). An earlier version of this file said 8, 16, and 26; the counts were corrected on 2 November 2026 from the raw answers in `results/`.

## Distinct findings and post hoc check against the HOL4 text

| # | Finding | Runs | Post hoc check |
|---|---|---|---|
| P1 | Sptree keeps duplicate keys, so toList/toAList differ from HOL4 | 3/3 | Correct. This is the known defect from the second proving round (tlookup_bij lemmas). |
| P2 | Sptree toList/toAList order is insertion order. HOL4 uses tree traversal order. | 3/3 | Correct. New. HOL4 toList = toListA [] over the tree. |
| P3 | CARD takes the length of an arbitrary enumeration that may contain duplicates | 3/3 | Correct. This is the known defect from the second proving round. |
| P4 | word_lsl/word_lsr by n >= width return the input instead of 0 (UInt shift is mod width) | 3/3 | Correct. New. HOL4 word_lsl_def and word_lsr_def give 0 for n >= width. To be confirmed in Lean. |
| P5 | word_asr wrong for n = 0 (gives all ones when msb is set, HOL4 gives w) and for n >= width | 3/3 | Correct. New. Follows from HOL4 word_asr_def. To be confirmed in Lean. |
| P6 | fp64_mul_add rounds twice, HOL4 FMA rounds once | 3/3 | Correct. The source comment already admits it as a translation gap. |
| P7 | Rounding modes collapsed to Unit and ignored | 3/3 | Correct. Documented in a source comment. |
| P8 | `end HOL4` / `open HOL4` without a namespace | 2/3 | Wrong. Artifact of the section split: `namespace HOL4` is in section 1. |
| P9 | Set operator precedences differ (∪ and \) | 1/3 | Difference by design (Table II), and the cause of the FV drift. |

## Not flagged by any run
- Finmap drops finiteness.
- LazyList does not enforce downward closure of `none`.
Both are documented representation choices in the source comments.

## Decision needed from the author
Accept or reject each of P1 to P9. Repairs are out of scope for this paper unless they are critical.

## Decision (2026-10-15)
The author confirmed: P1-P7 accepted, P8 and P9 rejected.
