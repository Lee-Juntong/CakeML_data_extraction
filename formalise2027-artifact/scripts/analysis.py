#!/usr/bin/env python3
"""Recompute the numbers reported in the paper (Tables I, III, VI, VII and the text) from the snapshots, the Lean
audit outputs (scripts/run_audit.sh), and the retained records.

Usage: python3 scripts/analysis.py [--work WORK] [--check expected/expected.json]

Writes results/paper_numbers.json and prints a comparison with the expected
values when --check is given.
"""
from __future__ import annotations

import argparse
import collections
import dataclasses
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))
import counter as C  # noqa: E402

C.SNAPSHOT_ROOT = ROOT / "snapshots"
REPO = Path(".")
BASE = "252eab2cf"
ACCEPTED = "af5ac084c"
ENDPOINTS = {"aef82615e": "Skills", "0d1173557": "Docs", "88927cb6f": "Second pass",
             "9f5188d63": "Hybrid", "41c815090": "Direct"}
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
ATTR = re.compile(r"^@\[[^\]\n]*\]\s*")
REPAIRED = "4841f993e"
# Suffixes of equation lemmas that Lean generates for a definition.
GEN_SUFFIX = re.compile(r"\.(eq_def|eq_\d+|eq_unfold|induct|unfold|fun_cases)$")
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'.!?]*")


def textual_closure_ok(decl, theorems):
    """True when no theorem reachable through theorem names in proof text is unproved."""
    def refs(d):
        body = d.content.split(":=", 1)[1] if ":=" in d.content else ""
        return {p for t in IDENT.findall(body) for p in set(t.split(".")) if p in theorems}
    seen, stack = set(), [decl]
    while stack:
        x = stack.pop()
        for nm in refs(x):
            for y in theorems[nm]:
                if (y.file, y.name) in seen:
                    continue
                seen.add((y.file, y.name))
                if not y.theorem_proved:
                    return False
                stack.append(y)
    return True


def decls(ref):
    return C.declarations_at_ref(REPO, ref)


def key_str(d):
    return d.file.removeprefix("lean_type_sound/LeanTypeSound/") + ":" + d.name


def norm_stmt(d):
    return re.sub(r"\s+", "", ATTR.sub("", d.content).split(":=", 1)[0])


def norm_body(d):
    t = re.split(r"\b(termination_by|decreasing_by)\b", ATTR.sub("", d.content))[0]
    return re.sub(r"\s+", "", re.sub(r"\bsorry\b", "", t))


def load_tsv(path):
    rows = []
    for line in open(path, encoding="utf-8"):
        parts = line.rstrip("\n").split("\t")
        while len(parts) < 4:
            parts.append("")
        rows.append(parts)
    return rows


def resolve(index, d):
    mod = "LeanTypeSound." + d.file[:-5]
    return [r for r in index.get(mod, []) if r[1] == d.name or r[1].endswith("." + d.name)]


def index_rows(rows):
    idx = collections.defaultdict(list)
    for r in rows:
        idx[r[0]].append(r)
    return idx


def strip_sml_comments(s):
    out, depth, i = [], 0, 0
    while i < len(s):
        if s.startswith("(*", i):
            depth += 1; i += 2; continue
        if depth and s.startswith("*)", i):
            depth -= 1; i += 2; continue
        if depth == 0:
            out.append(s[i])
        i += 1
    return "".join(out)


def hol4_counts(base_decls):
    hol = ROOT / "snapshots" / BASE / "lean_type_sound" / "hol4-ultramin"
    tot = collections.Counter()
    blocks = []
    lines = 0
    for f in sorted(hol.glob("*.sml")):
        raw = f.read_text(encoding="utf-8", errors="replace")
        lines += raw.count("\n")
        s = strip_sml_comments(raw)
        for k in ["Definition", "Theorem", "Inductive", "Datatype", "Type"]:
            tot[k] += len(re.findall(r"^%s\b" % k, s, re.M))
        for m in re.finditer(r"^Theorem\s+([A-Za-z0-9_']+)(\[[^\]]*\])?", s, re.M):
            blocks.append((m.group(1), f.name, m.group(2) or ""))
    def lean_file(sml):
        stem = sml[: -len("Script.sml")]
        parts = stem.split("_")
        name = "".join(p[:1].upper() + p[1:] for p in parts)
        return name + ".lean"

    by_file = collections.defaultdict(set)
    for d in base_decls:
        if d.group == "theorem":
            by_file[d.file].add(d.name)
    lean = set().union(*by_file.values())
    generated = {"evaluate_def", "evaluate_ind", "evaluate_decs_def", "evaluate_decs_ind",
                 "full_evaluate_def", "full_evaluate_ind"}
    gen, same, renamed, absent = [], [], [], []
    for b in blocks:
        here = by_file.get(lean_file(b[1]), set())
        if b[0] in generated:
            gen.append(b)
        elif b[0] in here:
            same.append(b)
        elif any(n in here for n in (b[0] + "_thm", b[0] + "_local")):
            renamed.append(b)
        else:
            absent.append(b)
    hol_names = {b[0] for b in blocks}
    renamed_targets = {n for b in renamed for n in (b[0] + "_thm", b[0] + "_local") if n in lean}
    extra = sorted(n for n in lean if n not in hol_names and n not in renamed_targets)
    return {
        "sml_files": len(list(hol.glob("*.sml"))), "sml_lines": lines,
        "definition_blocks": tot["Definition"], "inductive_blocks": tot["Inductive"],
        "datatypes": tot["Datatype"], "type_abbreviations": tot["Type"], "theorems": tot["Theorem"],
        "generated_by_lean": len(gen), "stated": len(same) + len(renamed), "renamed": len(renamed),
        "absent": len(absent), "absent_local": sum("local" in b[2] for b in absent),
        "absent_names": sorted(b[0] for b in absent), "extra_lean_theorems": extra,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--work", type=Path, default=ROOT / "work")
    ap.add_argument("--check", type=Path, default=None)
    args = ap.parse_args()
    W = args.work
    out = {}

    base, _ = decls(BASE)
    canon = [d for d in base if d.group == "theorem"]
    canon_defs = [d for d in base if d.group == "definition"]
    B = {d.key: d for d in base}
    out["hol4"] = hol4_counts(base)

    # Table I: layers by file.
    layer_of = {
        "HOL4Prelude.lean": "prelude",
        **{f: "syntax_namespaces_libraries" for f in ["Ast.lean", "Location.lean", "Namespace.lean", "NamespaceProps.lean",
                                                     "Misc.lean", "Mllist.lean", "Mlstring.lean", "LprefixLub.lean",
                                                     "FpSem.lean", "Ffi.lean"]},
        **{f: "semantic_primitives_evaluation" for f in ["SemanticPrimitives.lean", "SemanticPrimitivesProps.lean",
                                                        "Evaluate.lean", "EvaluateProps.lean", "SemanticsMin.lean"]},
        **{f: "type_system_weakening_soundness" for f in ["TypeSystem.lean", "TypeSysProps.lean", "Weakening.lean",
                                                         "TypeSoundInvariants.lean", "TypeSound.lean"]},
    }
    t1 = collections.defaultdict(lambda: {"definitions": 0, "theorems": 0})
    for d in base:
        f = d.file.removeprefix("lean_type_sound/LeanTypeSound/")
        t1[layer_of.get(f, "other:" + f)]["definitions" if d.group == "definition" else "theorems"] += 1
    out["table1"] = dict(t1)
    out["lean_lines"] = sum((C._snap(BASE) / f).read_text(encoding="utf-8").count("\n")
                            for f in C.files_at_ref(REPO, BASE))

    # Table III.
    res = C.analyze(REPO, BASE, C.DEFAULT_MILESTONES)
    out["table3"] = {r.commit: {"defs": r.translated_definitions, "stmts": r.translated_theorem_statements,
                                "coverage": r.translated_combined} for r in res}
    init, _ = decls("5dc5b8ba0")
    S0 = {d.key: d for d in init}
    miss_defs = sum(1 for d in canon_defs if d.key not in S0)
    miss_thms = sum(1 for d in canon if d.key not in S0)
    present = [S0[k] for k in B if k in S0]
    out["initial_partition"] = {
        "missing_definitions": miss_defs, "missing_theorems": miss_thms,
        "true_statements": sum(d.is_vacuous_true for d in present if d.group == "theorem"),
        "sorry_bodies": sum(1 for d in present if d.group == "definition" and d.kind != "opaque" and not d.is_partial
                            and C.DIRECT_BODY_STUB_RE.search(d.content)),
        "partial": sum(d.is_partial for d in present), "opaque": sum(d.kind == "opaque" for d in present),
    }

    # Acceptance state split.
    acc, _ = decls(ACCEPTED)
    SA = {d.key: d for d in acc}
    pre = th = pre_n = th_n = 0
    untranslated = []
    for k, d in B.items():
        s = SA.get(k)
        ok = s is not None and (s.definition_translated if d.group == "definition" else s.statement_translated)
        if d.file.endswith("HOL4Prelude.lean"):
            pre_n += 1; pre += ok
        else:
            th_n += 1; th += ok
        if d.group == "definition" and not ok:
            untranslated.append((d.file.split("/")[-1], d.name, "absent" if s is None else s.kind))
    out["acceptance"] = {"prelude": [pre, pre_n], "theory": [th, th_n],
                         "definitions_without_body": len(untranslated),
                         "by_file": dict(collections.Counter(u[0] for u in untranslated)),
                         "semantic_primitive_stubs": sorted(u[1] for u in untranslated if u[0] != "HOL4Prelude.lean")}

    # Statement taint on the baseline.
    taint_rows = load_tsv(W / "audit" / BASE / "stmt_taint.tsv")
    tidx = index_rows(taint_rows)
    taint = set()
    for d in canon:
        r = resolve(tidx, d)
        if len(r) == 1 and r[0][2] == "true":
            taint.add(key_str(d))
    roots_idx = index_rows(load_tsv(W / "audit" / BASE / "stmt_roots.tsv"))
    cat = collections.Counter()
    roots_of = {}
    for d in canon:
        r = resolve(roots_idx, d)
        rs = {x.split(":", 1)[1] for x in r[0][3].split(";") if x} if len(r) == 1 else set()
        roots_of[key_str(d)] = rs
        if key_str(d) in taint:
            g = set()
            for x in rs:
                if x.startswith("check_freevars"):
                    g.add("check_freevars")
                elif x in ("instBEqV", "instBEqSem_env"):
                    g.add("beq_values")
                elif any(t in x for t in ["evaluate", "pmatch", "do_eq", "v_to_list", "concrete_v", "v_to_char_list"]):
                    g.add("evaluator_semantic_primitives")
            for x in g:
                cat[x] += 1
    out["taint"] = {"tainted": len(taint), "by_category": dict(cat)}

    # Proof endpoints.
    kj = json.load(open(ROOT / "data" / "direct" / "kernel_41c815090.json"))
    kax = collections.defaultdict(list)
    for dd in kj["declarations"]:
        if dd["kind"] == "theorem":
            kax[dd["module"]].append((dd["name"], dd["axioms"]))
    table5 = {}
    per = {}
    admitted_base = {l.split("\t")[2].strip() for l in open(W / "audit" / BASE / "defsorry.tsv", encoding="utf-8")
                     if l.strip() and l.split("\t")[1] == "def"}
    closure_check = collections.defaultdict(collections.Counter)
    for c, lab in ENDPOINTS.items():
        ds, tokens = decls(c)
        S = {d.key: d for d in ds}
        if c != "41c815090":
            aidx = index_rows(load_tsv(W / "audit" / c / "axioms.tsv"))
        loc, aud, same_aud = set(), set(), 0
        perm, same_perm = set(), 0
        via_instances = set()
        s_ed = d_ed = 0
        theorems = collections.defaultdict(list)
        for d in ds:
            if d.group == "theorem":
                theorems[d.name.split(".")[-1]].append(d)
        for k, b in B.items():
            s = S.get(k)
            if s is None:
                continue
            if b.group == "definition":
                d_ed += norm_body(s) != norm_body(b)
                continue
            same = norm_stmt(s) == norm_stmt(b)
            s_ed += not same
            if not s.theorem_proved:
                continue
            loc.add(key_str(b))
            if c != "41c815090":
                r = resolve(aidx, b)
                ok = len(r) == 1 and set(a for a in r[0][2].split(",") if a) <= STANDARD
            else:
                mod = "LeanTypeSound." + b.file[:-5]
                r = [ax for n, ax in kax.get(mod, []) if n == b.name or n.endswith("." + b.name)]
                ok = len(r) == 1 and set(r[0]) <= STANDARD
            if ok:
                aud.add(key_str(b))
                same_aud += same
            # Complete modulo the baseline admissions: every sorry root is an admitted
            # definition of the frozen baseline (termination proofs, two BEq instances)
            # or an equation lemma that Lean generated for one.
            if ok:
                pok = True
            elif c != "41c815090":
                axs = set(a for a in r[0][2].split(",") if a)
                roots = [x.split(":", 1)[1] for x in r[0][3].split(";") if x] if len(r) == 1 else []
                pok = (len(r) == 1 and axs <= STANDARD | {"sorryAx"} and bool(roots)
                       and all(GEN_SUFFIX.sub("", x) in admitted_base for x in roots))
            else:
                # The Direct endpoint needs Mathlib, so its sorry roots are not recomputed.
                # Theorem references in the proof text are followed instead. This rule agrees
                # with the root based rule on every local proof of the four other endpoints.
                pok = set(r[0]) <= STANDARD | {"sorryAx"} and textual_closure_ok(s, theorems)
            if c != "41c815090":
                closure_check[lab]["agree" if textual_closure_ok(s, theorems) == pok else "disagree"] += 1
            if pok:
                perm.add(key_str(b))
                same_perm += same
                if c != "41c815090" and not ok and any("instBEq" in x for x in r[0][3].split(";")):
                    via_instances.add(key_str(b))
        fail = loc - aud
        table5[lab] = {"local": len(loc), "audited": len(aud), "fail_statement": len(fail & taint),
                       "fail_proof": len(fail - taint), "unchanged": same_aud, "statement_edits": s_ed,
                       "definition_edits": d_ed, "helpers": sum(k not in B for k in S),
                       "missing": sum(k not in S for k in B), "sorry_tokens": tokens,
                       "audited_tainted": len(aud & taint),
                       "modulo_admissions": len(perm), "unchanged_modulo": same_perm,
                       "modulo_reaching_beq_instances": sorted(k.split(":")[1] for k in via_instances),
                       "local_not_modulo": len(loc - perm), "modulo_not_audited": len(perm - aud)}
        per[lab] = {"local": loc, "audited": aud, "modulo": perm}
    out["table5"] = table5
    out["closure_rule_check"] = {k: dict(v) for k, v in closure_check.items()}
    U_loc = set().union(*[p["local"] for p in per.values()])
    U_aud = set().union(*[p["audited"] for p in per.values()])
    U_mod = set().union(*[p["modulo"] for p in per.values()])
    allt = {key_str(d) for d in canon}
    never = allt - U_aud
    out["union"] = {"local": len(U_loc), "audited": len(U_aud), "modulo_admissions": len(U_mod),
                    "never_modulo": len(allt - U_mod),
                    "never_modulo_by_file": dict(collections.Counter(k.split(":")[0] for k in allt - U_mod)),
                    "never_modulo_names_Mlstring": sorted(k.split(":")[1] for k in allt - U_mod if k.startswith("Mlstring")),
                    "main_theorem_modulo_anywhere": "TypeSound.lean:semantics_type_sound" in U_mod,
                    "never_audited": len(never),
                    "never_audited_tainted": len(never & taint),
                    "never_audited_tainted_by_file": dict(collections.Counter(k.split(":")[0] for k in never & taint)),
                    "never_audited_untainted_by_file": dict(collections.Counter(k.split(":")[0] for k in never - taint)),
                    "main_theorem_local_anywhere": "TypeSound.lean:semantics_type_sound" in U_loc}
    K = per["Skills"]
    out["skills_vs_second"] = {
        "modulo_only_second": len(per["Second pass"]["modulo"] - K["modulo"]),
        "modulo_only_skills": len(K["modulo"] - per["Second pass"]["modulo"]),
        "audited_only_second": len(per["Second pass"]["audited"] - K["audited"]),
        "audited_only_skills": len(K["audited"] - per["Second pass"]["audited"]),
    }
    D, P = per["Docs"], per["Second pass"]
    second_fail_taint = (P["local"] - P["audited"]) & taint
    out["docs_vs_second"] = {
        "local_only_second": len(P["local"] - D["local"]), "local_only_docs": len(D["local"] - P["local"]),
        "second_statement_failures_via_check_freevars": sum(
            any(x.startswith("check_freevars") for x in roots_of[k]) for k in second_fail_taint),
    }

    # Statement edits that add LawfulBEq.
    lawful = collections.Counter()
    names = set()
    for c in ENDPOINTS:
        ds, _ = decls(c)
        S = {d.key: d for d in ds}
        for d in canon:
            s = S.get(d.key)
            if s is None or norm_stmt(s) == norm_stmt(d):
                continue
            if "LawfulBEq" in s.content.split(":=", 1)[0] and "LawfulBEq" not in d.content.split(":=", 1)[0]:
                lawful["edits"] += 1
                names.add(key_str(d))
    out["lawfulbeq"] = {"edits": lawful["edits"], "theorems": len(names),
                        "by_file": dict(collections.Counter(n.split(":")[0] for n in names))}

    # Admitted definitions in the baseline and in Hybrid.
    for c in [BASE, "9f5188d63"]:
        p = W / "audit" / c / "defsorry.tsv"
        rows = [l.rstrip("\n").split("\t") for l in open(p, encoding="utf-8") if l.strip()]
        out.setdefault("admitted_definitions", {})[c] = sorted(r[2] for r in rows if r[1] == "def")

    # Refutations.
    out["refutations"] = {}
    for name in ["Refute_nsLookup_nsBind", "Refute_explode_thm"]:
        log = (W / "audit" / BASE / f"{name}.log").read_text()
        out["refutations"][name] = {"error": "error" in log.lower(), "log": log.strip()[-300:]}

    # Repaired translation (snapshot 4841f993e).
    rep, _ = decls(REPAIRED)
    R = {d.key: d for d in rep}
    rows = [l.rstrip("\n").split("\t") for l in open(W / "audit" / REPAIRED / "defsorry.tsv", encoding="utf-8") if l.strip()]
    rep_admitted = sorted(r[2] for r in rows if r[1] == "def")
    src = ROOT / "snapshots" / REPAIRED / "lean_type_sound" / "LeanTypeSound"
    termination_only = all(
        re.search(r"\bsorry\b", re.split(r"\b(termination_by|decreasing_by)\b",
                                          ATTR.sub("", R[k].content))[0]) is None
        for k in R if R[k].group == "definition")
    rt = index_rows(load_tsv(W / "audit" / REPAIRED / "stmt_taint.tsv"))
    rep_taint = sum(1 for d in canon if (lambda r: len(r) == 1 and r[0][2] == "true")(resolve(rt, d)))
    rr = index_rows(load_tsv(W / "audit" / REPAIRED / "stmt_roots.tsv"))
    beq_roots = sum(1 for d in canon for r in resolve(rr, d) if "instBEq" in r[3])
    changed_stmt = sorted(key_str(B[k]) for k in B if B[k].group == "theorem" and k in R
                          and norm_stmt(R[k]) != norm_stmt(B[k]))
    # The counter attributes an inductive relation to the declaration before it, so
    # the comparison stops at the next inductive and the relation is compared on its own.
    def own(d):
        return dataclasses.replace(d, content=re.split(r"\n(?:mutual\s+)?inductive\s", d.content)[0])
    changed_def = sorted(key_str(B[k]) for k in B if B[k].group == "definition" and k in R
                         and norm_body(own(R[k])) != norm_body(own(B[k])))
    rel = lambda ref: re.search(r"inductive type_v .*?(?=\n(?:/-|inductive|def|theorem|mutual|end)\b)",
                                C.read_at_ref(REPO, ref, "lean_type_sound/LeanTypeSound/TypeSoundInvariants.lean"), re.S).group(0)
    type_v_ctors = lambda t: dict(re.findall(r"\n  \| (\w+) :(.*?)(?=\n  \| |\Z)", t, re.S))
    tb, tr = type_v_ctors(rel(BASE)), type_v_ctors(rel(REPAIRED))
    changed_ctor = sorted(c for c in tb if re.sub(r"\s+", "", tb[c]) != re.sub(r"\s+", "", tr.get(c, "")))
    chk = (W / "audit" / REPAIRED / "Check_repairs.log").read_text()
    axioms_lines = [l for l in chk.splitlines() if "depends on axioms" in l or "does not depend" in l]
    rcov = C.analyze(REPO, BASE, [("repaired", REPAIRED, "Repaired translation")])[0]
    out["repaired"] = {
        "coverage": [rcov.translated_definitions, rcov.translated_theorem_statements, rcov.translated_combined],
        "definitions": sum(1 for d in rep if d.group == "definition" and d.key in B),
        "theorems": sum(1 for d in rep if d.group == "theorem" and d.key in B),
        "missing": sum(1 for k in B if k not in R),
        "added": sum(1 for k in R if k not in B),
        "admitted_definitions": rep_admitted,
        "admitted_definitions_count": len(rep_admitted),
        "definition_sorry_only_in_termination": termination_only,
        "statement_taint": rep_taint,
        "statements_reaching_beq_instance": beq_roots,
        "statement_edits": len(changed_stmt),
        "lawfulbeq_binders_added": sum(R[k].content.split(":=", 1)[0].count("LawfulBEq")
                                       - B[k].content.split(":=", 1)[0].count("LawfulBEq")
                                       for k in B if B[k].group == "theorem" and k in R),
        "statement_edits_by_file": dict(collections.Counter(k.split(":")[0] for k in changed_stmt)),
        "definition_edits": changed_def,
        "type_v_constructor_edits": changed_ctor,
        "check_repairs_errors": "error" in chk.lower(),
        "check_repairs_nonstandard": [l for l in axioms_lines if "sorryAx" in l],
        "check_repairs_theorems": len(axioms_lines),
        "refutations_fail": {n: "error" in (W / "audit" / REPAIRED / f"{n}.log").read_text().lower()
                             for n in ["Refute_nsLookup_nsBind", "Refute_explode_thm"]},
    }

    # Vacuous statements (Vacuous.lean): conclusion True, or two sides equal at
    # reducible transparency, such as P <-> P.
    out["vacuous"] = {}
    for c in [BASE, REPAIRED]:
        vidx = index_rows(load_tsv(W / "audit" / c / "vacuous.tsv"))
        out["vacuous"][c] = sorted(key_str(d) for d in canon if resolve(vidx, d))
    cc = (W / "audit" / REPAIRED / "Check_computed.log").read_text()
    out["repaired"]["check_computed_errors"] = "error" in cc.lower()
    out["repaired"]["check_computed_axioms"] = sorted(
        l.split("depends on axioms:")[1].strip() for l in cc.splitlines() if "depends on axioms" in l)

    resdir = ROOT / "results"
    resdir.mkdir(exist_ok=True)
    json.dump(out, open(resdir / "paper_numbers.json", "w"), indent=1, sort_keys=True)
    print(f"wrote {resdir / 'paper_numbers.json'}")

    if args.check:
        exp = json.load(open(args.check))
        bad = 0
        for path, want in exp.items():
            cur = out
            for part in path.split("/"):
                cur = cur[part] if isinstance(cur, dict) else cur[int(part)]
            ok = cur == want
            bad += not ok
            print(f"{'PASS' if ok else 'FAIL'}  {path}: got {cur!r}, expected {want!r}")
        print(f"\n{len(exp) - bad} of {len(exp)} checks pass")
        sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
