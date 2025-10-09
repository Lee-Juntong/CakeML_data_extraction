import os
import re
import sys
import json
from typing import List, Dict

THEOREM_START_RE = re.compile(
    r"^\s*Theorem\s+(?P<name>[A-Za-z0-9_']+)\s*:\s*(?P<after>.*)$"
)
PROOF_LINE_RE = re.compile(r"^\s*Proof\b")

DEF_START_RE = re.compile(
    r"^\s*Definition\s+(?P<name>[A-Za-z0-9_']+)\s*:\s*(?P<after>.*)$"
)
DEF_END_RE   = re.compile(r"^\s*End\b")

def extract_theorems_from_lines(lines: List[str]) -> List[Dict]:
    out = []
    i, n = 0, len(lines)
    while i < n:
        m = THEOREM_START_RE.match(lines[i])
        if not m:
            i += 1
            continue
        name = m.group("name")
        after = m.group("after").rstrip("\n")
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
        i = j + 1
    return out

def extract_definitions_from_lines(lines: List[str]) -> List[Dict]:
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

def extract_from_file(filepath: str) -> List[Dict]:
    try:
        with open(filepath, encoding="utf-8") as f:
            lines = f.read().splitlines()
    except Exception as e:
        print(f"Warning: failed to read {filepath}: {e}", file=sys.stderr)
        return []
    items = extract_theorems_from_lines(lines) + extract_definitions_from_lines(lines)
    for it in items:
        it["source_file"] = filepath
    return items

def extract_from_dir(input_dir: str) -> List[Dict]:
    all_items = []
    for root, dirs, files in os.walk(input_dir):
        for fname in files:
            if fname.lower().endswith(".sml"):
                full = os.path.join(root, fname)
                items = extract_from_file(full)
                all_items.extend(items)
    return all_items

def main():
    if len(sys.argv) != 3:
        print("Usage: python extract_multi.py input_directory output.json", file=sys.stderr)
        sys.exit(1)
    input_dir = sys.argv[1]
    output_path = sys.argv[2]
    items = extract_from_dir(input_dir)
    with open(output_path, "w", encoding="utf-8") as outf:
        json.dump(items, outf, ensure_ascii=False, indent=2)
    print(f"Processed directory {input_dir}, extracted {len(items)} items into {output_path}")

if __name__ == "__main__":
    main()