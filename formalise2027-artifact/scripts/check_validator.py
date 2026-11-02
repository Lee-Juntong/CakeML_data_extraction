#!/usr/bin/env python3
"""Recompute the validator counts of Table IV and the finding list of Table V
from the retained validator records."""
import collections
import csv
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
V = ROOT / "data" / "validator"


def load(p):
    s = open(p, encoding="utf-8").read()
    dec = json.JSONDecoder(strict=False)
    i, out = 0, []
    while i < len(s):
        while i < len(s) and s[i].isspace():
            i += 1
        if i >= len(s):
            break
        o, j = dec.raw_decode(s, i)
        out.append(o)
        i = j
    return out


def summary(records):
    pairs = collections.Counter()
    right = flagged = failed = findings = 0
    misrouted = []
    for r in records:
        lean = (r.get("lean_path") or "").replace("\\", "/").split("/")[-1].lower().replace(".lean", "")
        base = r.get("base", "").replace("_", "")
        if lean.replace("_", "") != base:
            misrouted.append((r.get("base"), lean))
        if r.get("status") == "right":
            right += 1
        elif r.get("errors"):
            flagged += 1
            findings += len(r["errors"])
        else:
            failed += 1
    return {"calls": len(records), "right_calls": right, "flagged_pairs": flagged, "findings": findings,
            "failed_calls": failed, "misrouted_calls": misrouted}


r3 = summary(load(V / "round3_results.jsonl"))
r4 = summary(load(V / "round4_results.jsonl"))
esc = json.load(open(V / "round4_escalated.json"))
print("round 3:", r3)
print("round 4:", r4)
print("round 4 escalated items:", len(esc), [e.get("base") for e in esc] if isinstance(esc, list) else esc)
rows = list(csv.DictReader(open(ROOT / "data" / "findings.csv", encoding="utf-8")))
verdicts = collections.Counter(r["post_hoc_verdict"].split(";")[0] for r in rows)
print("Table V findings:", len(rows), dict(verdicts))
ok = (r3["right_calls"] == 13 and r3["flagged_pairs"] == 7 and r3["findings"] == 8 and r3["failed_calls"] == 0
      and r4["flagged_pairs"] == 6 and r4["findings"] == 7 and r4["failed_calls"] == 1
      and len(r4["misrouted_calls"]) == 1 and r4["right_calls"] == 13 and len(rows) == 15
      and r3["findings"] + r4["findings"] == len(rows))
print("PASS" if ok else "FAIL", "validator record checks (round 4: 13 right calls, one of them misrouted, so 12 pairs right)")

# Rounds 5 and 6: three runs each of the round 4 prompt with Gemini 3.8 Flash, on the
# frozen baseline (round 5) and on the repaired translation (round 6).
import zipfile  # noqa: E402


def later_round(rnd, commit):
    d = V / f"round{rnd}"
    rows = list(csv.DictReader(open(ROOT / "data" / f"findings_round{rnd}.csv", encoding="utf-8")))
    good_all = True
    # The inputs are the 20 HOL4 scripts, the 20 paired Lean files, and the prelude of the commit.
    snap = ROOT / "snapshots" / commit / "lean_type_sound"
    hol4 = ROOT / "snapshots" / "252eab2cf" / "lean_type_sound"
    zf = zipfile.ZipFile(d / f"inputs_{commit}.zip")
    inp = [n for n in zf.namelist() if n.endswith((".sml", ".lean"))]
    same = 0
    for n in inp:
        kind, f = n.split("inputs/", 1)[-1].split("/", 1)
        where = snap / "LeanTypeSound" / f if kind == "lean" else next(hol4.rglob(f"hol4-ultramin/**/{f}"), None)
        same += where is not None and where.read_bytes() == zf.read(n)
    print(f"round {rnd} inputs: {len(inp)} files, {same} identical to snapshot {commit}")
    good_all &= len(inp) == same and same >= 40
    for run in (1, 2, 3):
        recs = [json.loads(l) for l in open(d / f"run{run}.jsonl", encoding="utf-8") if l.strip()]
        st = collections.Counter(r["status"] for r in recs)
        nf = sum(len(r.get("errors", [])) for r in recs)
        mine = [x for x in rows if x["run"] == str(run)]
        claims = sorted((r["base"], i) for r in recs for i, _ in enumerate(r.get("errors", [])))
        listed = sorted((x["record_base"], int(x["index"])) for x in mine)
        good = len(recs) == 20 and len({r["base"] for r in recs}) == 20 and claims == listed and st["failed"] == 0
        good_all &= good
        print(f"round {rnd} run {run}: {len(recs)} calls, {dict(st)}, {nf} findings, "
              f"verdicts {dict(collections.Counter(x['verdict'] for x in mine))}", "PASS" if good else "FAIL")
    print(f"round {rnd} defects found per run:",
          dict(collections.Counter((x["defect"], x["run"]) for x in rows if x["defect"] != "none")))
    return good_all


ok = later_round(5, "252eab2cf") and ok
ok = later_round(6, "4841f993e") and ok
print("PASS" if ok else "FAIL", "all validator record checks")
sys.exit(0 if ok else 1)
