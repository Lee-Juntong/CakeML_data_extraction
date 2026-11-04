# Artifact: Migrating CakeML Type Soundness from HOL4 to Lean with LLM Agents

Artifact for the FormaliSE 2027 experience report "Migrating CakeML Type Soundness
from HOL4 to Lean with LLM Agents: An Experience Report".

The artifact recomputes the numbers in Tables IV, VII, VIII, and IX of the paper and the
counts in the text of Sections II, IV, V, and VI from exported repository states and
retained records, and checks the validator counts of Table V and the findings of
Tables VI and VIII against the validator records. It rebuilds the frozen Lean baseline,
the four Claude Code proving endpoints of the first round, and the repaired translation with Lean 4.29.1,
runs the transitive axiom audit, the statement taint check, and the statement
preservation check, replays the two Lean refutations of frozen statements, and
checks the Lean proofs of the repaired statements and the semantic scan for vacuous statements.

## Contents

| Path | Content |
|---|---|
| `snapshots/<commit>/` | The `lean_type_sound` directory of the CakeML fork at 20 commits: the seven translation milestones of Table IV, the proof pilot `98d240248`, the frozen baseline `252eab2cf`, the five proving endpoints, and the repaired translation `4841f993e` (branch `lean-translate-round5-repair`, two repair commits on `252eab2cf`, Lean sources only), and the five endpoints of the second proving round, `578cf6024` (Skills), `8faa2c0ff` (Docs), `6df3c625f` (Second pass), `a26ded4c6` (Hybrid), and `904068958` (Direct), the heads of the fork's `lean-translate-*` branches (Lean sources and the May session logs only; the round 2 session logs are in `data/proof_round2/`). Each has a `COMMIT.json` with the full hash, date, and author. The reduced HOL4 package is in `snapshots/252eab2cf/lean_type_sound/hol4-ultramin/`. Agent session logs are in `claude-logs/`. |
| `data/validator/` | Validator records: `round3_results.jsonl`, `round4_results.jsonl`, the two escalated round 4 pairs (`round4_escalated.json`), the earlier two stage runs of 26 March (`earlier_runs_26mar.jsonl`), and the validator notebook with its prompts (`compare_validate.ipynb`). `round5/` and `round6/` hold the three runs of rounds 5 and 6 with Gemini 3.8 Flash (`run1.jsonl` to `run3.jsonl`, `run_log.json`), the scripts that produced them, and their input files (`inputs_252eab2cf.zip` for the frozen baseline, `inputs_4841f993e.zip` for the repaired translation). |
| `data/direct/kernel_41c815090.json` | Recorded axiom audit of the Direct endpoint, which imports Mathlib. |
| `data/review_rounds.json` | Reconstruction of review rounds 1 to 4 (Table V). Rounds 5 and 6 are in `data/validator/`. |
| `data/findings.csv` | The 15 validator findings of Table VI with handling and post hoc verdicts. |
| `data/findings_round5.csv`, `data/findings_round6.csv` | Every finding of rounds 5 and 6 with our verdict against the HOL4 sources and the defect of Table VIII it matches. Round 6 has no finding. |
| `data/hol4_library_evidence.md` | HOL4 library excerpts behind the post hoc verdicts (fixities, finite map updates, folds, `mergesort_tail`). |
| `scripts/counter.py` | The structural counter (the manifest of Section II, Table IV, local proof counts). |
| `scripts/build.py`, `scripts/run_audit.sh` | Rebuild the baseline and endpoints and run the Lean audit scripts. |
| `scripts/lean/` | `Axioms.lean` (transitive axiom audit), `StmtTaint.lean` and `StmtRoots.lean` (statement taint), `DefSorry.lean` (admitted definitions), the refutations `Refute_nsLookup_nsBind.lean` and `Refute_explode_thm.lean`, `Check_repairs.lean` (proofs of the repaired statements), `Check_computed.lean` (proofs of the expanded `do_app_cases` and `type_op_cases`), and `Vacuous.lean` (statements that are trivially true, such as `P ↔ P`). |
| `scripts/analysis.py` | Recomputes all numbers and compares them with `expected/expected.json`. |
| `scripts/check_validator.py` | Recomputes the validator counts of Table V and checks Table VI and the R5 column of Table VIII against the records. |
| `paper.pdf` | The paper as submitted to FormaliSE 2027 (anonymous version). |
| `run_all.sh`, `Dockerfile`, `build_image.sh` | Entry point, image definition, and image export with SHA256 checksum. |

## Proving endpoints

The paper calls the Hybrid workflow "Aristotle offered". This README, the scripts, and the
records keep the name Hybrid.

| Commit | Workflow in the paper | Session log in `claude-logs/` |
|---|---|---|
| `aef82615e` | Skills: one pass with the Skills prompt | `2026-04-30-175234-*.txt` |
| `0d1173557` | Docs: the Docs prompt, a correction by the operator, and a second pass. An earlier session with another prompt was reverted (`2026-05-06-140851-*.txt`) | `2026-05-06-205529-objective.txt` to `2026-05-06-213911-objective.txt` |
| `88927cb6f` | Second pass: the Skills prompt and a second pass | `2026-05-06-224734-*.txt` |
| `9f5188d63` | Hybrid: Claude Code with the Aristotle MCP server connected, a prompt for dependency order, annotations, and delegation to Aristotle, and a second pass. The session log has no Aristotle call | `2026-05-08-000722-*.txt` |
| `41c815090` | Direct: the whole project submitted to Aristotle with Lean 4.28.0 | `ARISTOTLE_SUMMARY.md` |

## Requirements

- Hardware: any x86_64 or arm64 machine with 2 cores, 4 GB of RAM, and 4 GB of free disk.
- Docker, or for a native run: Python 3.9 or later, git, Lean 4.29.1, and a checkout of
  [batteries](https://github.com/leanprover-community/batteries) at commit
  `756e3321fd3b02a85ffda19fef789916223e578c`.
- No network access is needed at run time. Building the image downloads Lean and batteries.

## Running

With Docker:

```
docker build -t cakeml-lean-migration:1.0 .      # or: docker load < cakeml-lean-migration-1.0-amd64.tar.gz
docker run --rm cakeml-lean-migration:1.0
```

Natively:

```
export LEAN=/path/to/lean-4.29.1/bin/lean
export BATTERIES=/path/to/batteries        # at commit 756e3321
bash run_all.sh
```

The run takes about 8 minutes on 2 cores. Step 4 prints `PASS Table IX equals the recorded table_r2.json`, and the run ends with

```
181 of 181 checks pass
```

and writes all recomputed values to `results/paper_numbers.json`.

## What each step reproduces

| Paper item | Step | Output |
|---|---|---|
| Section II: HOL4 counts (255 definition blocks, 280 theorems, 266 stated, 8 absent), 8,352 Lean lines | `analysis.py` | `hol4`, `lean_lines` |
| Section II: manifest of 382 definitions and 269 theorems, 112 definitions in the prelude | `analysis.py` | `table1` |
| Table IV, initial defect partition (21, 40, 229, 57, 10, 3) | `counter.py`, `analysis.py` | `table3`, `initial_partition` |
| Section IV: 61 definitions without bodies at acceptance (54 in the prelude, 7 semantic primitives) | `analysis.py` | `acceptance` |
| Table V validator counts, misrouted FpSem call, failed Weakening call, escalated pairs, round 5 runs and inputs | `check_validator.py` | console |
| Section V and the R5 column of Table VIII: 5 round 5 findings, all correct | `data/findings_round5.csv`, `check_validator.py` | console |
| Section V and Table V: round 6, all 60 calls right | `data/validator/round6/`, `check_validator.py` | console |
| Table VI | `data/findings.csv`, `data/hol4_library_evidence.md`, `check_validator.py` | console |
| Section VI-A: 120 tainted statements, 106 / 24 / 16 | `StmtTaint.lean`, `StmtRoots.lean`, `analysis.py` | `taint` |
| Table VII (all columns) and the Any row | `Axioms.lean`, `analysis.py` | `table5`, `union` |
| Completion modulo admissions: Lean roots for four endpoints, text rule for Direct, agreement of the two rules | `Axioms.lean`, `analysis.py` | `table5/*/modulo_admissions`, `closure_rule_check` |
| Section VI-D and Table VIII, repaired translation: coverage, admitted definitions, taint, edits, refutations fail, proofs of repaired statements | `DefSorry.lean`, `StmtTaint.lean`, `Check_repairs.lean`, `Check_computed.lean`, `analysis.py` | `repaired` |
| Sections VI-C and VI-D, vacuous statements: 9 in the baseline (7 trivial in HOL4 too, plus `do_app_cases` and `type_op_cases`), 7 after the repair | `Vacuous.lean`, `analysis.py` | `vacuous` |
| Supporting numbers, not in the current text: Skills versus Second pass in round 1 (same prompt, one and two passes) | `analysis.py` | `skills_vs_second` |
| Supporting numbers, not in the current text: Docs versus Second pass in round 1 (24 via `check_freevars`) | `analysis.py` | `docs_vs_second` |
| Section VI-C: 50 LawfulBEq edits to 28 theorems | `analysis.py` | `lawfulbeq` |
| Section VI-C: refutations of `nsLookup_nsBind` and `explode_thm` | `Refute_*.lean` | `refutations` |
| Section VI-C: residual 118 modulo admissions, by file | `analysis.py` | `union` |
| Admitted definitions in the baseline and in Hybrid | `DefSorry.lean` | `admitted_definitions` |
| Table IX, proof completion of round 2 on the 269 canonical theorems of the repaired translation, from the recorded axiom audits and the exported round 2 endpoints. The script counts Direct's two restated theorems (`tlookup_bij_suff`, `tlookup_bij_iff`) as Mod. and Aud. (269); the paper reports 267 for these two columns because it excludes the restated theorems until their repair is reviewed | `data/proof_round2/results/audit/table_r2.py --snapshots snapshots` | console, `table_r2.json` |

## What the artifact cannot reproduce

- The LLM runs themselves: the translation by Claude Code, the Gemini validator runs
  (rounds 3 to 6), and the five proving runs. They depend on hosted models and are not deterministic.
  The artifact contains their outputs (repository states and records) and the session
  logs that were kept.
- The human decisions in the review rounds. Table V and the handling column of
  Table VI are reconstructed from commit messages, the validator records, and project
  notes.
- A fresh audit of the Direct endpoint, which imports Mathlib. The artifact uses the
  recorded audit in `data/direct/kernel_41c815090.json`.
- The size of the original 47 file package before the dependency reduction (about
  29,000 lines). The reduction commits are in the CakeML fork.
- The cost record (about 0.7 million tokens per run of the validation and refinement
  stage) comes from the author's dissertation.

## Provenance

The snapshots are exported with `git archive` from the CakeML fork
<https://github.com/Lee-Juntong/cakeml> (branch `lean-translate` and one branch per
proving workflow). The directories `hol4/` and `hol4-min/` of the original package are
omitted. The validator records of rounds 3 and 4 come from
<https://github.com/Lee-Juntong/CakeML_data_extraction>. `round3_results.jsonl` is
the author's local copy of `compare_validate_results_old_2.jsonl`. It holds the same
20 records as `compare_validate_results.jsonl` at commit `599be60` of that repository
and differs only in whitespace. The round 5 and round 6 records were produced on 5 October 2026 with
`data/validator/round5/round5_validate.py` and `data/validator/round6/round6_validate.py`,
which send the round 4 prompt of `compare_validate.ipynb` (commit `013b67c`) to
Gemini 3.8 Flash with the high reasoning setting, at temperature 0.1, through an
OpenAI compatible endpoint. The two scripts differ only in their input file.

The repaired translation was written by Claude under the author's direction after
the study, in two commits on the branch `lean-translate-round5-repair`: `405848cad`
repairs six defects, and `4841f993e` states the computed theorems `do_app_cases` and
`type_op_cases` in full. Each repair follows the HOL4 text. A human expert triaged and
adjudicated the round 5 findings. As in every round of the study, the
build, the structural checks, and the next review round check the repairs.

The counter in `scripts/counter.py` accepts declarations with attributes such as
`@[simp] theorem`. An earlier version did not, which made 13 proved Hybrid theorems
look absent in the dissertation.

## Additions of November 2026

This section lists the records added after the artifact archive of 9 October 2026. The Docker entry point recomputes Table IX from them (step 4 of `run_all.sh`, from the recorded axiom audits and the exported round 2 endpoints in `snapshots/`); the other files are records and Lean files to check by hand. The final translation is commit `de795c9f6` on branch `lean-translate` of the CakeML fork; the README text above still names the earlier repair `4841f993e` on branch `lean-translate-round5-repair`, which was not pushed. Its tree is identical to `de795c9f6`, which carries the same two repair commits rebased onto `lean-translate`.

| Path | Content |
|---|---|
| `data/validator/round7/` | Round 7, the review of the library file `HOL4Prelude.lean` at `de795c9f6` against the HOL4 library definitions it names. `pairs/` holds the 8 section pairs and `INDEX.md` with the sha256 of each fetched HOL4 file; `results/run1` to `run3` hold the 24 raw validator answers; `validator_prompt.md` is the prompt; `ROUND7_FINDINGS.md` lists the distinct findings and the author's decisions. The answers contain 9 `RIGHT` and 15 error reports with 27 error items. |
| `data/proof_round2/` | The second proving round of October 2026: the setup and run scripts, the prompts, the Claude Code settings, and per workflow (`skills`, `docs`, `second-pass`, `hybrid`, `direct`) the session logs and run logs. `results/proof_round2.bundle` is a Git bundle of the five `proof2-*` branches. `results/audit/` holds the statement and definition diffs (`stmt_diff_out.txt`, `def_diff_out.txt`), the table script and its output (`table_r2.py`, `table_out.txt`, `table_r2.json`), the audit scripts, and the Lean checks `Refute_tlookup_bij.lean` and `Check_CARD.lean`. `table_r2.py` recomputes Table IX from the recorded axiom audits `results/audit/<workflow>/axioms.tsv` and a clone of the CakeML fork: `python table_r2.py /path/to/cakeml` (or set `CAKEML`), or without a clone from the exported endpoints in `snapshots/`: `python table_r2.py --snapshots snapshots`, as `run_all.sh` does. It uses `scripts/counter.py` of this artifact and the fork's branches `lean-translate-*`, whose heads equal the bundle's `proof2-*` heads; `stages.py` gives Direct's local count after each Aristotle task in the same way. `results/audit/PRIM_SEM_ENV_NOTE.md` and `results/primsemenv/` record the translation of `prim_type_sound_invariants` and its Aristotle proof. In the session logs, the operator's e-mail address is replaced by `[redacted]`. |
| `data/evidence/` | Lean files behind the claims about rewritten definitions and the library: `OldEqualsNew*.lean` and `OrigEquations*.lean` (rewritten definitions against the originals), `Closure.lean`, `Closure2.lean`, `CardDeps.lean` (closure of the main theorem), `PreludeDefects.lean` with its output (the word shift and `fp64_mul_add` defects of round 7, checked by `decide`), and `Observe.lean` with its output (which defects reach the closure of the main theorem and of each manifest statement). `PrimSemEnv.lean` is the translation of `prim_type_sound_invariants` with Aristotle's proof, from branch `lean-translate-prim-sem-env` of the fork (commit `cdee629213`). `ind2.py` compares the declarations outside the manifest at all ten endpoints (`python ind2.py /path/to/cakeml`). |

## Computers, tool versions, and costs

| Stage | Computer | Tools | Cost |
|---|---|---|---|
| Translation and review rounds 1 to 4 (Feb to Apr 2026) | The computers of the human experts who ran them; their specifications were not recorded | Claude Code with Claude Opus 4.6 (rounds 1 to 3) and Claude Opus 4.7 (definition pass); validator Gemini 2.5 Pro at temperature 0.1 | About 0.7 million validator tokens per run of the validation and refinement stage (author's dissertation); agent costs not recorded |
| Proof round 1 (May 2026) | As above | Claude Code with Claude Opus 4.7; Direct: Aristotle on Lean 4.28.0 | Not recorded |
| Review rounds 5 and 6 (5 Oct 2026) | Windows 10 Pro (build 19045) workstation, 16 cores, 64 GB RAM | `gemini-3.8-flash-high`, temperature 0.1, top_p 0.95, through an OpenAI compatible endpoint | About 0.35 million tokens and 10 minutes per run (`run_log.json`), about US$2 per round of three runs |
| Proof round 2, repairs, and `prim_type_sound_invariants` (Oct 2026) | Same workstation (`data/proof_round2/results/tools_check.txt`) | Claude Code 2.1.287 and 2.1.296 with Claude Opus 4.7, effort xhigh, plugin lean4-skills 4.11.3; Aristotle through aristotlelib 2.1.0 on Lean 4.28.0 | Claude Code, API-equivalent cost reported at the end of each session (`run_log.txt`): Skills US$21.73, Docs US$35.05, Second pass US$190.97, Hybrid US$46.61; Aristotle cost not recorded |
| Review round 7 (15 Oct 2026) | A Claude Code session; computer not recorded | Claude Haiku 5.5 run as a subagent, no temperature setting | Not recorded separately |
| This artifact | Any x86_64 or arm64 machine (see Requirements) | Lean 4.29.1, batteries `756e3321`, Python 3.9 or later | About 8 minutes on 2 cores |

## License

The scripts and data written for this artifact are released under the BSD 3-Clause
License (`LICENSE`). The snapshots contain CakeML sources under CakeML's BSD 3-Clause
License. Lean and batteries, downloaded when the image is built, are under the Apache
License 2.0.
