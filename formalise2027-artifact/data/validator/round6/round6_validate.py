#!/usr/bin/env python3
"""Round 6 validator: compare the 20 HOL4 theory scripts with the Lean files of
the repaired translation (commit 4841f993e, branch lean-translate-round5-repair), using the prompt of round 4
(CakeML_data_extraction/compare_validate.ipynb, commit 013b67c), through an
OpenAI-compatible endpoint.

Usage (PowerShell):
    python round6_validate.py                     # model chosen from /v1/models
    python round6_validate.py --model <model-id>  # explicit model
    python round6_validate.py --list-models

The API key is read from the environment variable GEMINI_API_KEY and is never
printed or written to disk. Only the Python standard library is used.
Outputs go to ./results/run<k>.jsonl and ./results/run_log.json.
"""
from __future__ import annotations

import argparse
import json
import os
import sys
import time
import urllib.error
import urllib.request
import zipfile
from pathlib import Path

HERE = Path(__file__).resolve().parent

# Pairs in the order of the round 4 notebook: (base, HOL4 script, Lean file).
PAIRS = [
    ("ast", "astScript.sml", "Ast.lean"),
    ("evaluate", "evaluateScript.sml", "Evaluate.lean"),
    ("evaluateprops", "evaluatePropsScript.sml", "EvaluateProps.lean"),
    ("ffi", "ffiScript.sml", "Ffi.lean"),
    ("fpsem", "fpSemScript.sml", "FpSem.lean"),
    ("location", "locationScript.sml", "Location.lean"),
    ("misc", "miscScript.sml", "Misc.lean"),
    ("mllist", "mllistScript.sml", "Mllist.lean"),
    ("mlstring", "mlstringScript.sml", "Mlstring.lean"),
    ("namespace", "namespaceScript.sml", "Namespace.lean"),
    ("namespaceprops", "namespacePropsScript.sml", "NamespaceProps.lean"),
    ("semanticprimitives", "semanticPrimitivesScript.sml", "SemanticPrimitives.lean"),
    ("semanticprimitivesprops", "semanticPrimitivesPropsScript.sml", "SemanticPrimitivesProps.lean"),
    ("typesound", "typeSoundScript.sml", "TypeSound.lean"),
    ("typesoundinvariants", "typeSoundInvariantsScript.sml", "TypeSoundInvariants.lean"),
    ("typesysprops", "typeSysPropsScript.sml", "TypeSysProps.lean"),
    ("typesystem", "typeSystemScript.sml", "TypeSystem.lean"),
    ("weakening", "weakeningScript.sml", "Weakening.lean"),
    ("lprefix_lub", "lprefix_lubScript.sml", "LprefixLub.lean"),
    ("semantics_min", "semantics_minScript.sml", "SemanticsMin.lean"),
]

# Prompt text copied verbatim from the round 4 notebook.
SYSTEM_INSTRUCTIONS = """\
You are reviewing a translation from HOL4/CakeML SML theory scripts to Lean 4 code.
Find genuine translation errors only. Missing/simplified Lean proofs are acceptable unless they change meaning.
If correct, output exactly RIGHT. Otherwise output STRICT JSON only.
"""

ERROR_SCHEMA_TEXT = """{
  \"base\": string,
  \"status\": \"error\",
  \"summary\": string,
  \"errors\": [{
    \"kind\": string,
    \"severity\": \"low\" | \"medium\" | \"high\",
    \"hol4_evidence\": string,
    \"lean_evidence\": string,
    \"why_wrong\": string
  }],
  \"confidence\": number,
  \"notes\": string
}"""


def build_prompt(base: str, hol4_text: str, lean_text: str) -> str:
    return f"""\
File pair base name: {base}


Task: compare HOL4 and Lean. Report only translation errors. You may report more than one error per pair if needed, but be concise.
Output contract:
- If no non-proof translation error: RIGHT
- Else: STRICT JSON with schema:
{ERROR_SCHEMA_TEXT}

--- HOL4 source text ---
{hol4_text}

--- Lean source text ---
{lean_text}
"""


def read_inputs() -> dict[str, str]:
    """Return {relative path: text} from inputs_4841f993e.zip or ./inputs/."""
    files: dict[str, str] = {}
    z = HERE / "inputs_4841f993e.zip"
    if z.exists():
        with zipfile.ZipFile(z) as zf:
            for n in zf.namelist():
                if n.endswith((".sml", ".lean")):
                    files[n.split("inputs/", 1)[-1]] = zf.read(n).decode("utf-8", errors="replace")
    else:
        for p in (HERE / "inputs").rglob("*"):
            if p.suffix in (".sml", ".lean"):
                files[str(p.relative_to(HERE / "inputs")).replace("\\", "/")] = p.read_text(encoding="utf-8", errors="replace")
    return files


def http_json(url: str, key: str, payload: dict | None = None, timeout: int = 600) -> dict:
    data = None if payload is None else json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(url, data=data, method="GET" if payload is None else "POST")
    req.add_header("Authorization", f"Bearer {key}")
    req.add_header("Content-Type", "application/json")
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return json.loads(resp.read().decode("utf-8"))


def list_models(base_url: str, key: str) -> list[str]:
    out = http_json(base_url.rstrip("/") + "/models", key)
    return sorted(m.get("id", "") for m in out.get("data", []))


def parse_answer(text: str):
    stripped = text.strip()
    if stripped.startswith("```"):
        lines = stripped.splitlines()
        if len(lines) >= 2:
            stripped = "\n".join(l for l in lines[1:] if not l.strip().startswith("```")).strip()
    if stripped.upper() == "RIGHT":
        return "RIGHT"
    try:
        return json.loads(stripped)
    except json.JSONDecodeError:
        s, e = stripped.find("{"), stripped.rfind("}")
        if s != -1 and e > s:
            return json.loads(stripped[s : e + 1])
        raise


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--base-url", default=os.getenv("VALIDATOR_BASE_URL", "http://127.0.0.1:8317/v1"))
    ap.add_argument("--model", default=os.getenv("VALIDATOR_MODEL", ""))
    ap.add_argument("--runs", type=int, default=3)
    ap.add_argument("--temperature", type=float, default=0.1)
    ap.add_argument("--list-models", action="store_true")
    ap.add_argument("--only", default="", help="comma separated pair bases to run")
    args = ap.parse_args()

    key = os.getenv("GEMINI_API_KEY")
    if not key:
        print("GEMINI_API_KEY is not set in this shell.", file=sys.stderr)
        return 2

    try:
        models = list_models(args.base_url, key)
    except Exception as e:  # noqa: BLE001
        print(f"Could not list models at {args.base_url}: {e}", file=sys.stderr)
        models = []
    if args.list_models:
        print("\n".join(models))
        return 0
    model = args.model
    if not model:
        cands = [m for m in models if "3.8" in m and "flash" in m.lower()]
        if not cands:
            print("No model with '3.8' and 'flash' in its id. Available:\n  " + "\n  ".join(models), file=sys.stderr)
            return 3
        model = sorted(cands, key=len)[0]
    print(f"model: {model}  endpoint: {args.base_url}  runs: {args.runs}", flush=True)

    files = read_inputs()
    outdir = HERE / "results"
    outdir.mkdir(exist_ok=True)
    selected = [p for p in PAIRS if not args.only or p[0] in args.only.split(",")]
    log = {"model": model, "base_url": args.base_url, "temperature": args.temperature, "top_p": 0.95,
           "baseline_commit": "4841f993e", "prompt_source": "CakeML_data_extraction compare_validate.ipynb at 013b67c",
           "started": time.strftime("%Y-%m-%dT%H:%M:%S%z"), "runs": []}
    for run in range(1, args.runs + 1):
        path = outdir / f"run{run}.jsonl"
        done = set()
        if path.exists():
            for line in path.read_text(encoding="utf-8").splitlines():
                try:
                    done.add(json.loads(line)["base"])
                except Exception:  # noqa: BLE001
                    pass
        run_info = {"run": run, "calls": []}
        for i, (base, sml, lean) in enumerate(selected, 1):
            if base in done:
                continue
            hol4_text = files[f"hol4/{sml}"]
            lean_text = files[f"lean/{lean}"]
            prompt = SYSTEM_INSTRUCTIONS + "\n" + build_prompt(base, hol4_text, lean_text)
            payload = {"model": model, "temperature": args.temperature, "top_p": 0.95,
                       "messages": [{"role": "user", "content": prompt}]}
            t0 = time.time()
            rec = {"base": base, "hol4_file": sml, "lean_file": lean, "run": run, "model": model, "stage": 1}
            try:
                out = http_json(args.base_url.rstrip("/") + "/chat/completions", key, payload)
                text = (out.get("choices") or [{}])[0].get("message", {}).get("content") or ""
                rec["usage"] = out.get("usage", {})
                rec["raw_text"] = text
                ans = parse_answer(text)
                if ans == "RIGHT":
                    rec.update({"status": "right", "errors": []})
                else:
                    rec.update({k: v for k, v in ans.items() if k not in ("base",)})
                    rec["status"] = "error"
            except urllib.error.HTTPError as e:
                rec.update({"status": "failed", "errors": [], "notes": f"HTTP {e.code}: {e.read()[:500]!r}"})
            except Exception as e:  # noqa: BLE001
                rec.update({"status": "failed", "errors": [], "notes": f"{type(e).__name__}: {e}"})
            rec["seconds"] = round(time.time() - t0, 1)
            with path.open("a", encoding="utf-8") as f:
                f.write(json.dumps(rec, ensure_ascii=False) + "\n")
            run_info["calls"].append({"base": base, "status": rec["status"], "seconds": rec["seconds"],
                                      "usage": rec.get("usage", {})})
            print(f"run {run} [{i}/{len(selected)}] {base}: {rec['status']} "
                  f"({len(rec.get('errors', []))} findings, {rec['seconds']}s)", flush=True)
            time.sleep(0.5)
        log["runs"].append(run_info)
    log["finished"] = time.strftime("%Y-%m-%dT%H:%M:%S%z")
    (outdir / "run_log.json").write_text(json.dumps(log, indent=1), encoding="utf-8")
    print(f"done. results in {outdir}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
