#!/usr/bin/env python3
"""Count translation and proof progress across selected repository states.

The script reads the Lean files of each state either from Git objects of the
CakeML fork (--repo) or from the exported snapshots shipped with the artifact
(--snapshots, the default in the artifact).  It uses the clean proof baseline (252eab2cf) as a fixed set
of translation obligations.  This prevents agent-added helper lemmas from
artificially increasing later completion percentages.

This is a static audit, not a proof of semantic equivalence.  Translation and
auto-proving are deliberately separate metrics:

* A definition is translated when its body is present (not an `opaque`,
  `partial def`, or direct `sorry`/`admit` stub).  A `sorry` in
  `decreasing_by` is a proof obligation and does not make the definition body
  untranslated.
* A theorem statement is translated when it is present and not the vacuous
  placeholder `True`.
* A theorem is proved when its translated declaration contains no
  `sorry`/`admit`.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable


DEFAULT_MILESTONES = [
    ("initial_one_shot", "5dc5b8ba0", "Initial one-shot Claude translation"),
    ("dependency_repair", "1802597dc", "Dependency-aware repair and missing definitions"),
    ("theorem_statement_pass", "5a3f2e5a4", "Dedicated theorem-statement translation pass"),
    ("audit_pass", "a47e17267", "Definition/statement audit pass"),
    ("true_stub_cleanup", "b01347d3e", "Vacuous True-stub cleanup"),
    ("cross_model_validation", "af5ac084c", "Gemini comparison, validation, and refinement"),
    ("claude_direct", "98d240248", "Direct Claude proof attempt"),
    ("claude_definition_completion", "dbb89adda", "Claude definition-completion pass"),
    ("clean_proof_baseline", "252eab2cf", "Clean proof baseline"),
    ("claude_lean_skills", "aef82615e", "Claude with Lean skills"),
    # The original remote branch was deleted after its result was retained under
    # a more descriptive branch name. Pin the recorded experiment to its commit
    # so pruning stale remote refs does not break historical reproduction.
    ("claude_docs", "0d1173557a", "Claude with tactic-document access"),
    (
        "claude_docs_two_pass",
        "88927cb6f",
        "Claude with tactic docs, two passes",
    ),
    (
        "claude_aristotle_hybrid",
        "9f5188d63",
        "Claude Code orchestrating Aristotle MCP, two passes",
    ),
    (
        "direct_aristotle",
        "41c815090",
        "Whole-folder direct Aristotle run",
    ),
]

TRANSLATION_MILESTONES = {
    "initial_one_shot",
    "dependency_repair",
    "theorem_statement_pass",
    "audit_pass",
    "true_stub_cleanup",
    "cross_model_validation",
    "claude_definition_completion",
    "clean_proof_baseline",
}

PROOF_MILESTONES = {
    "claude_direct",
    "clean_proof_baseline",
    "claude_lean_skills",
    "claude_docs",
    "claude_docs_two_pass",
    "claude_aristotle_hybrid",
    "direct_aristotle",
}

DECL_RE = re.compile(
    r"(?m)^(?:@\[[^\]\n]*\]\s*)?(?P<prefix>(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*)"
    r"(?P<kind>def|opaque|theorem|lemma)\s+"
    r"(?P<name>[^\s(:={]+)"
)
SORRY_RE = re.compile(r"\b(?:sorry|admit)\b")
VACUOUS_TRUE_RE = re.compile(r":\s*True\s*$", re.MULTILINE)
DIRECT_BODY_STUB_RE = re.compile(r":=\s*(?:by\s*)?(?:sorry|admit)\b")


@dataclass(frozen=True)
class Declaration:
    file: str
    group: str
    kind: str
    name: str
    occurrence: int
    prefix: str
    content: str

    @property
    def key(self) -> tuple[str, str, str, int]:
        return (self.file, self.group, self.name, self.occurrence)

    @property
    def has_placeholder(self) -> bool:
        return bool(SORRY_RE.search(self.content))

    @property
    def is_vacuous_true(self) -> bool:
        if self.group != "theorem":
            return False
        header = self.content.split(":=", 1)[0].rstrip()
        return bool(VACUOUS_TRUE_RE.search(header))

    @property
    def is_partial(self) -> bool:
        return self.group == "definition" and "partial" in self.prefix.split()

    @property
    def statement_translated(self) -> bool:
        return self.group == "theorem" and not self.is_vacuous_true

    @property
    def definition_translated(self) -> bool:
        return (
            self.group == "definition"
            and self.kind != "opaque"
            and not self.is_partial
            and not DIRECT_BODY_STUB_RE.search(self.content)
        )

    @property
    def theorem_proved(self) -> bool:
        return self.statement_translated and not self.has_placeholder


@dataclass
class MilestoneResult:
    milestone: str
    ref: str
    commit: str
    date: str
    label: str
    canonical_definitions: int
    translated_definitions: int
    definition_pct: float
    canonical_theorems: int
    translated_theorem_statements: int
    theorem_statement_pct: float
    translated_combined: int
    canonical_combined: int
    translation_pct: float
    proved_theorems: int
    theorem_proof_pct: float
    missing_canonical: int
    helper_declarations: int
    snapshot_declarations: int
    placeholder_declarations: int
    sorry_tokens: int
    opaque_definitions: int
    partial_definitions: int
    vacuous_true_theorems: int


SNAPSHOT_ROOT: Path | None = None


def git(repo: Path, *args: str) -> str:
    command = ["git", "-c", "safe.directory=*", "-C", str(repo), *args]
    proc = subprocess.run(command, check=True, text=True, encoding="utf-8", errors="replace", capture_output=True)
    return proc.stdout


def strip_lean_comments(text: str) -> str:
    """Remove nested Lean comments while preserving newlines and strings."""
    out: list[str] = []
    i = 0
    block_depth = 0
    in_line = False
    in_string = False
    escaped = False
    while i < len(text):
        ch = text[i]
        nxt = text[i + 1] if i + 1 < len(text) else ""
        if in_line:
            if ch == "\n":
                in_line = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue
        if block_depth:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.extend((" ", " "))
                i += 2
            elif ch == "-" and nxt == "/":
                block_depth -= 1
                out.extend((" ", " "))
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue
        if in_string:
            out.append(ch)
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            i += 1
            continue
        if ch == "-" and nxt == "-":
            in_line = True
            out.extend((" ", " "))
            i += 2
        elif ch == "/" and nxt == "-":
            block_depth = 1
            out.extend((" ", " "))
            i += 2
        else:
            out.append(ch)
            if ch == '"':
                in_string = True
            i += 1
    return "".join(out)


def _snap(ref: str) -> Path:
    assert SNAPSHOT_ROOT is not None
    short = ref.split("/")[-1]
    for d in SNAPSHOT_ROOT.iterdir():
        if d.is_dir() and (short.startswith(d.name) or d.name.startswith(short)):
            return d
    raise FileNotFoundError(f"no snapshot for {ref} under {SNAPSHOT_ROOT}")


def read_at_ref(repo: Path, ref: str, file: str) -> str:
    if SNAPSHOT_ROOT is not None:
        return (_snap(ref) / file).read_text(encoding="utf-8", errors="replace")
    return git(repo, "show", f"{ref}:{file}")


def files_at_ref(repo: Path, ref: str) -> list[str]:
    if SNAPSHOT_ROOT is not None:
        base = _snap(ref)
        return sorted(str(p.relative_to(base)) for p in (base / "lean_type_sound" / "LeanTypeSound").rglob("*.lean"))
    tree = git(repo, "ls-tree", "-r", "--name-only", ref, "--", "lean_type_sound/LeanTypeSound")
    return sorted(line for line in tree.splitlines() if line.endswith(".lean"))


def declarations_at_ref(repo: Path, ref: str) -> tuple[list[Declaration], int]:
    declarations: list[Declaration] = []
    sorry_tokens = 0
    for file in files_at_ref(repo, ref):
        raw = read_at_ref(repo, ref, file)
        clean = strip_lean_comments(raw)
        sorry_tokens += len(SORRY_RE.findall(clean))
        matches = list(DECL_RE.finditer(clean))
        relative = file.removeprefix("lean_type_sound/LeanTypeSound/")
        occurrences: dict[tuple[str, str], int] = {}
        for index, match in enumerate(matches):
            end = matches[index + 1].start() if index + 1 < len(matches) else len(clean)
            kind = match.group("kind")
            group = "theorem" if kind in {"theorem", "lemma"} else "definition"
            occurrence_key = (group, match.group("name"))
            occurrence = occurrences.get(occurrence_key, 0)
            occurrences[occurrence_key] = occurrence + 1
            declarations.append(
                Declaration(
                    file=relative,
                    group=group,
                    kind=kind,
                    name=match.group("name"),
                    occurrence=occurrence,
                    prefix=match.group("prefix").strip(),
                    content=clean[match.start():end],
                )
            )
    duplicates = _duplicates(d.key for d in declarations)
    if duplicates:
        duplicate_text = ", ".join("/".join(map(str, key)) for key in sorted(duplicates))
        raise RuntimeError(f"Duplicate declaration keys at {ref}: {duplicate_text}")
    return declarations, sorry_tokens


def _duplicates(items: Iterable[tuple[str, str, str, int]]) -> set[tuple[str, str, str, int]]:
    seen: set[tuple[str, str, str, int]] = set()
    duplicate: set[tuple[str, str, str, int]] = set()
    for item in items:
        if item in seen:
            duplicate.add(item)
        seen.add(item)
    return duplicate


def pct(numerator: int, denominator: int) -> float:
    return round(100.0 * numerator / denominator, 2) if denominator else 0.0


def analyze(repo: Path, baseline: str, milestones: list[tuple[str, str, str]]) -> list[MilestoneResult]:
    baseline_decls, _ = declarations_at_ref(repo, baseline)
    canonical = {decl.key: decl for decl in baseline_decls}
    canonical_defs = sum(decl.group == "definition" for decl in baseline_decls)
    canonical_theorems = sum(decl.group == "theorem" for decl in baseline_decls)

    results: list[MilestoneResult] = []
    for milestone, ref, label in milestones:
        declarations, sorry_tokens = declarations_at_ref(repo, ref)
        snapshot = {decl.key: decl for decl in declarations}
        canonical_snapshot = [snapshot.get(key) for key in canonical]
        present = [decl for decl in canonical_snapshot if decl is not None]
        translated_defs = sum(decl.definition_translated for decl in present)
        statement_theorems = sum(decl.group == "theorem" and decl.statement_translated for decl in present)
        translated_combined = translated_defs + statement_theorems
        proved_theorems = sum(decl.group == "theorem" and decl.theorem_proved for decl in present)
        if SNAPSHOT_ROOT is not None:
            meta = json.loads((_snap(ref) / "COMMIT.json").read_text())
            commit, date = meta["short"], meta["date"]
        else:
            commit = git(repo, "rev-parse", "--short", ref).strip()
            date = git(repo, "show", "-s", "--format=%ad", "--date=short", ref).strip()
        results.append(
            MilestoneResult(
                milestone=milestone,
                ref=ref,
                commit=commit,
                date=date,
                label=label,
                canonical_definitions=canonical_defs,
                translated_definitions=translated_defs,
                definition_pct=pct(translated_defs, canonical_defs),
                canonical_theorems=canonical_theorems,
                translated_theorem_statements=statement_theorems,
                theorem_statement_pct=pct(statement_theorems, canonical_theorems),
                translated_combined=translated_combined,
                canonical_combined=len(canonical),
                translation_pct=pct(translated_combined, len(canonical)),
                proved_theorems=proved_theorems,
                theorem_proof_pct=pct(proved_theorems, canonical_theorems),
                missing_canonical=sum(decl is None for decl in canonical_snapshot),
                helper_declarations=sum(decl.key not in canonical for decl in declarations),
                snapshot_declarations=len(declarations),
                placeholder_declarations=sum(decl.has_placeholder for decl in declarations),
                sorry_tokens=sorry_tokens,
                opaque_definitions=sum(decl.kind == "opaque" for decl in declarations),
                partial_definitions=sum(decl.is_partial for decl in declarations),
                vacuous_true_theorems=sum(decl.is_vacuous_true for decl in declarations),
            )
        )
    return results


def print_table(results: list[MilestoneResult]) -> None:
    print("TRANSLATION PHASE")
    print(
        "milestone|commit|defs translated|def %|statements translated|statement %|"
        "overall translation %"
    )
    for row in (item for item in results if item.milestone in TRANSLATION_MILESTONES):
        print(
            f"{row.milestone}|{row.commit}|"
            f"{row.translated_definitions}/{row.canonical_definitions}|{row.definition_pct:.2f}|"
            f"{row.translated_theorem_statements}/{row.canonical_theorems}|{row.theorem_statement_pct:.2f}|"
            f"{row.translation_pct:.2f}"
        )

    print("\nAUTO-PROVING PHASE")
    print("milestone|commit|canonical theorems proved|proof %|sorry tokens|helpers|canonical names missing")
    for row in (item for item in results if item.milestone in PROOF_MILESTONES):
        print(
            f"{row.milestone}|{row.commit}|"
            f"{row.proved_theorems}/{row.canonical_theorems}|{row.theorem_proof_pct:.2f}|"
            f"{row.sorry_tokens}|{row.helper_declarations}|{row.missing_canonical}"
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=None, help="Path to a CakeML fork Git repository")
    parser.add_argument("--snapshots", type=Path, default=Path(__file__).resolve().parent.parent / "snapshots",
                        help="Directory of exported repository states (used unless --repo is given)")
    parser.add_argument("--baseline", default="252eab2cf")
    parser.add_argument("--json", action="store_true", help="Emit JSON instead of a compact table")
    args = parser.parse_args()

    global SNAPSHOT_ROOT
    if args.repo is None:
        SNAPSHOT_ROOT = args.snapshots.resolve()
        repo = Path(".")
    else:
        repo = args.repo.resolve()
    results = analyze(repo, args.baseline, DEFAULT_MILESTONES)
    if args.json:
        print(json.dumps([asdict(row) for row in results], indent=2, ensure_ascii=False))
    else:
        print_table(results)


if __name__ == "__main__":
    main()
