# PrimSemEnv: port of prim_type_sound_invariants (2026-10-15)

Worktree `r2\primsemenv`, branch `prim-sem-env`, cut from `proof2-direct` (904068958d). Not pushed.

## Translation

- HOL4 source: `hol4/primTypesScript.sml` (74 lines, all 5 definitions), `hol4/primSemEnvScript.sml` (77 lines; the statement of `prim_type_sound_invariants`, 9 lines), and `unknown_loc_def` from `locationScript.sml` (3 lines). In total, about 80 HOL4 lines were translated (definitions and statement; the 50-line HOL4 proof was not translated).
- Lean: `LeanTypeSound/PrimSemEnv.lean`, 198 lines (172 non-blank). It is added to the root `LeanTypeSound.lean`.
- Definitions added: `unknown_loc`, `prim_types_program`, `add_to_sem_env`, `prim_sem_env`, `prim_tenv`, `prim_type_ids`. The theorem `prim_type_sound_invariants` has proof `sorry`. No existing file was changed, and no mismatch with existing definitions was found.
- Not translated: `prim_sem_env_eq`. HOL4 states it as `EVAL ``prim_sem_env ffi```, so the source has no statement text.
- One adaptation: HOL4 `THE` returns an unspecified value on `NONE`. Lean `THE` needs `Inhabited`, so the statement passes an explicit default with `@THE _ ⟨…⟩`. That default is never used, because `prim_sem_env ffi0` is `some _`; `#eval!` gives next_type_stamp 2 and next_exn_stamp 4.
- Model used for the translation: Claude Opus 5.5 (Claude Code).

## Aristotle

- Prompt: "Fill in all sorries of the theorems" (same as the Direct run). aristotlelib 2.1.0. Project 3773a8ea-d368-4eae-a1e6-1c37a3de5db0, task 54483eae-9ba6-4b18-93a0-8a4a7ad04521.
- Outcome: COMPLETE on the first task, about 15 minutes (submitted 18:49:39, done by 19:04:50 local). No continuation needed.
- Build: `lake build` succeeds, with no sorry in PrimSemEnv.lean.
- `#print axioms prim_type_sound_invariants`: propext, Classical.choice, Quot.sound. `semantics_type_sound` is unchanged and uses the same three.
- Edits: Aristotle changed only `PrimSemEnv.lean` (plus `ARISTOTLE_SUMMARY.md`). The diff deletes one line (`sorry`) and adds the rest. The statement and all six translated definitions are unchanged. It added the import `LeanTypeSound.NamespaceProps`, the new helper definitions `prim_ctor_env`, `prim_st`, `prim_ctMap_list`, and `prim_ctMap` (the ctMap witness from the HOL4 proof), and helper lemmas (`prim_sem_env_eq`, `ev_dexn`, `ev_dtype`, `prim_tenv_ok`, `prim_good_ctMap`, `prim_consistent_ctMap`, `prim_type_all_env`, `prim_type_s`, `prim_ctMap_range`, …). The Lean file is now 474 lines.

## Commits (branch prim-sem-env, author Lee-Juntong)

- e3ef57f66c: translation, proof `sorry` (before Aristotle)
- cdee629213: Aristotle result

Run script: `proof_round2/run_primsemenv.ps1`; logs are in `proof_round2/results/primsemenv/`. The snapshot is in `r2\primsemenv_stage1`.
