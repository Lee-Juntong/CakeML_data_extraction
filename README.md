# CakeML Data Extraction

Research tooling and intermediate data for extracting declarations from CakeML's HOL4 theory scripts, translating them to Lean 4 with Gemini, and reviewing the resulting translations.

The repository currently focuses on four CakeML theories—`ast`, `location`, `namespace`, and `namespaceProps`—and includes the source SML files, extracted JSON, generated Lean code, validation results, and refined Lean outputs.

## What is included

- `extract.py` extracts theorems, definitions, and datatypes from one HOL4 SML script.
- `extract_multi.py` processes a directory of SML scripts while preserving declaration order and recording theory metadata, ancestors, types, and overload substitutions.
- `translate_hol4_to_lean.ipynb` uses the Gemini API to translate extracted declarations to Lean 4 in dependency order.
- `compare_validate.ipynb` asks Gemini to compare HOL4/Lean file pairs, records suspected translation errors, and generates candidate fixes.
- `afterwork.ipynb` contains follow-up Lean diagnostics and repair experiments.
- `extracted/CML_Lean/` is the generated Lean 4 package.
- `refined_lean_TS/` contains refined Lean translations produced during validation.

The checked-in extraction covers 180 declarations:

| Kind | Count |
| --- | ---: |
| Types | 5 |
| Datatypes | 23 |
| Definitions | 41 |
| Theorems | 111 |

## Requirements

- Python 3
- Jupyter Notebook or JupyterLab for the notebook workflows
- A Gemini API key for translation and model-assisted validation
- Lean 4 and Lake for checking the generated Lean package

The notebooks install `google-generativeai` when needed. Some validation cells contain machine-specific source paths; update their configuration cells before running them on another system.

## Extract HOL4 declarations

Process all `.sml` files in a directory:

```bash
python extract_multi.py to_be_extracted extracted
```

Or process a single file:

```bash
python extract.py to_be_extracted/locationScript.sml extracted/locationScript.json
```

Each extracted item is represented as JSON with fields such as `kind`, `name`, `statement`, `theory`, and `ancestors`.

## Translate to Lean 4

Set the Gemini API key before opening `translate_hol4_to_lean.ipynb`:

```powershell
$env:GEMINI_API_KEY = "your-api-key"
```

Run the notebook from top to bottom. It translates the extracted JSON files sequentially so later theories can reuse context from earlier translations, then writes Lean modules under `extracted/CML_Lean/`.

The translation workflow is experimental and may emit placeholders such as `sorry`. Generated declarations should be reviewed against the original HOL4 sources before they are treated as equivalent.

## Check the generated Lean package

From the generated package directory, run:

```bash
cd extracted/CML_Lean
lake build
```

You can then open `extracted/CML_Lean/` as the workspace root in an editor with Lean 4 support.

## Validate and refine translations

`compare_validate.ipynb` pairs `xxxScript.sml` files with their corresponding `xxx.lean` files. It stores resumable model-review results in JSONL, filters suspected errors, and writes candidate corrected files to `refined_lean_TS/`.

Before running it:

1. Update `HOL4_ROOT` and `LEAN_ROOT` in the notebook.
2. Set `GEMINI_API_KEY`.
3. Review `MAX_FILES` and the selected Gemini model.
4. Run the notebook cells in order.

Model-generated diagnostics and fixes are review aids, not formal verification. The authoritative check remains comparison with the HOL4 source plus successful Lean elaboration and proof completion.

## Repository layout

```text
to_be_extracted/       HOL4/CakeML SML inputs
extracted/             Extracted JSON and generated Lean package
refined_lean_TS/       Candidate refined Lean translations
extract.py             Single-file declaration extractor
extract_multi.py       Directory-level declaration extractor
translate_hol4_to_lean.ipynb
compare_validate.ipynb
afterwork.ipynb
compare_validate_*.json[l]
```
