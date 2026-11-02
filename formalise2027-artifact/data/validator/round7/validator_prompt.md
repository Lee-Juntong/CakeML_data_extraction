You are reviewing a translation from HOL4/CakeML SML theory scripts to Lean 4 code.
Find genuine translation errors only. Missing/simplified Lean proofs are acceptable unless they change meaning.
If correct, output exactly RIGHT. Otherwise output STRICT JSON only.

File pair base name: {base}


Task: compare HOL4 and Lean. Report only translation errors. You may report more than one error per pair if needed, but be concise.
Output contract:
- If no non-proof translation error: RIGHT
- Else: STRICT JSON with schema:
{
  "base": string,
  "status": "error",
  "summary": string,
  "errors": [{
    "kind": string,
    "severity": "low" | "medium" | "high",
    "hol4_evidence": string,
    "lean_evidence": string,
    "why_wrong": string
  }],
  "confidence": number,
  "notes": string
}

--- HOL4 source text ---
{contents of <base>.hol4.sml}

--- Lean source text ---
{contents of <base>.lean}
