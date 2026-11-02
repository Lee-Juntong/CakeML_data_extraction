# Proof round 2: save the result of one run.
# Run in Windows PowerShell after the run ends, for example:
#   powershell -ExecutionPolicy Bypass -File E:\NUS\mcomp\Dissertation\publication\formalise2027\proof_round2\finish_run.ps1 -Run skills
# The script commits on the run's own branch. It does not push.

# Use -Message N to save only a snapshot after message N, before you send the next message.
param(
    [Parameter(Mandatory = $true)]
    [ValidateSet('skills', 'second-pass', 'docs', 'hybrid', 'direct')]
    [string]$Run,
    [int]$Message = 0
)
$ErrorActionPreference = 'Stop'
$Pub  = 'E:\NUS\mcomp\Dissertation\publication\formalise2027'
$Kit  = Join-Path $Pub 'proof_round2'
$Root = 'E:\NUS\mcomp\Dissertation\r2'
$dir  = Join-Path $Root $Run
$proj = Join-Path $dir 'lean_type_sound'
$out  = Join-Path $Kit "results\$Run"
New-Item -ItemType Directory -Force $out | Out-Null

if ($Message -gt 0) {
    git -C $dir add -A
    git -C $dir commit -m "Proof round 2: $Run, state after message $Message"
    git -C $dir log --oneline -1
    return
}

# 1. Move the text logs of /export into claude-logs, as in May.
$logs = Join-Path $proj 'claude-logs'
Get-ChildItem $proj -File -Filter '20*.txt' | ForEach-Object {
    Copy-Item $_.FullName $out -Force
    Move-Item $_.FullName $logs -Force
}

# 2. Copy the full session transcripts (.jsonl) of this folder.
if ($Run -ne 'direct') {
    $tag = "r2-$Run-lean"
    $found = Get-ChildItem (Join-Path $env:USERPROFILE '.claude\projects') -Directory | Where-Object { $_.Name -like "*$tag*" }
    if (-not $found) { Write-Warning "No transcript folder matches *$tag*. Copy the .jsonl files by hand. See README.md, step 6." }
    foreach ($f in $found) { Copy-Item (Join-Path $f.FullName '*') $out -Recurse -Force }
    $jsonl = Get-ChildItem $out -Recurse -Filter '*.jsonl'
    $calls = 0
    if ($jsonl) {
        $calls = ($jsonl | Select-String -Pattern '"name":"mcp__aristotle__', '"command":"[^"]*aristotle' | Measure-Object).Count
    }
    Write-Host "Aristotle tool calls in the transcripts of ${Run}: $calls"
    if ($Run -ne 'hybrid' -and $calls -gt 0) { Write-Warning "$Run must have no Aristotle call. Tell Claude." }
    if ($Run -eq 'hybrid' -and $calls -eq 0) { Write-Host 'Hybrid made no Aristotle call (as in May). Write this in RUN_LOG.md.' }
}

# 3. Commit all changes on the run's branch.
git -C $dir add -A
git -C $dir commit -m "Proof round 2: $Run endpoint"
if ($LASTEXITCODE -ne 0) { Write-Warning 'Nothing to commit, or the commit failed.' }
git -C $dir log --oneline -3
Write-Host "Saved. Transcripts and logs are in $out"
