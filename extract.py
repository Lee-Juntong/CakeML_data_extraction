
"""
Extract Theorem and Definition declarations from HOL4/CakeML SML scripts

  - Block theorems starting with “Theorem NAME: … Proof … QED”
  - Definition blocks “Definition NAME: … End”
"""

import re
import sys
import json
from typing import List, Dict

# Regex for Theorem header
THEOREM_START_RE = re.compile(
    r"^\s*Theorem\s+(?P<name>[A-Za-z0-9_']+)\s*:\s*(?P<after>.*)$"
)
PROOF_LINE_RE = re.compile(r"^\s*Proof\b")

# Regex for Definition block
DEF_START_RE = re.compile(
    r"^\s*Definition\s+(?P<name>[A-Za-z0-9_']+)\s*:\s*(?P<after>.*)$"
)
DEF_END_RE   = re.compile(r"^\s*End\b")

def extract_theorems(lines: List[str]) -> List[Dict]:
    out = []
    i, n = 0, len(lines)
    while i < n:
        m = THEOREM_START_RE.match(lines[i])
        if not m:
            i += 1
            continue
        name = m.group("name")
        after = m.group("after").rstrip("\n")
        # collect statement lines until “Proof”
        stmt_lines = [after] if after else []
        j = i + 1
        while j < n and not PROOF_LINE_RE.match(lines[j]):
            stmt_lines.append(lines[j].rstrip("\n"))
            j += 1
        statement = "\n".join(stmt_lines).strip()
        out.append({
            "kind": "Theorem",
            "name": name,
            "statement": statement
        })
        i = j + 1  # skip past “Proof” (or end)
    return out

def extract_definitions(lines: List[str]) -> List[Dict]:
    out = []
    i, n = 0, len(lines)
    while i < n:
        m = DEF_START_RE.match(lines[i])
        if not m:
            i += 1
            continue
        name = m.group("name")
        after = m.group("after").rstrip("\n")
        body_lines = [after] if after else []
        j = i + 1
        while j < n and not DEF_END_RE.match(lines[j]):
            body_lines.append(lines[j].rstrip("\n"))
            j += 1
        statement = "\n".join(body_lines).strip()
        out.append({
            "kind": "Definition",
            "name": name,
            "statement": statement
        })
        i = j + 1
    return out

def extract_from_file(path: str) -> List[Dict]:
    with open(path, encoding="utf-8") as f:
        lines = f.read().splitlines()
    theos = extract_theorems(lines)
    defs = extract_definitions(lines)
    items = theos + defs
    return items

def main():
    if len(sys.argv) != 3:
        print("Usage: python extract_thm_def_to_file.py input.sml output.json", file=sys.stderr)
        sys.exit(1)
    in_path = sys.argv[1]
    out_path = sys.argv[2]
    items = extract_from_file(in_path)

    with open(out_path, "w", encoding="utf-8") as f_out:
        json.dump(items, f_out, ensure_ascii=False, indent=2)
    print(f"Extracted {len(items)} items -> {out_path}")

if __name__ == "__main__":
    main()
