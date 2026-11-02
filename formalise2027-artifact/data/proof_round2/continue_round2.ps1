# Proof round 2: continue after a stop. Double-click continue_round2.cmd to run this script.
# 1. Checks the Aristotle key and the Aristotle MCP server.
# 2. Switches the Hybrid folder to Lean 4.28.0 and Mathlib v4.28.0 (Aristotle requires this version).
# 3. Prepares Claude Code again (prep_claude.ps1).
# 4. Starts Direct in a second window, if it has not started yet.
# 5. Continues Second pass, then runs Docs and Hybrid. Finished runs are skipped.
#    A usage limit makes the script wait until the limit resets; it then continues by itself.
# 6. Restores the Claude Code setup and writes the result bundle.
# Nothing is pushed. All logs go to proof_round2\results\.
$ErrorActionPreference = 'Stop'
$Kit  = 'E:\NUS\mcomp\Dissertation\publication\formalise2027\proof_round2'
$Root = 'E:\NUS\mcomp\Dissertation\r2'
$res  = Join-Path $Kit 'results'
Start-Transcript -Path (Join-Path $res 'continue_round2_transcript.txt') -Append | Out-Null
function Step([string]$m) { Write-Host ''; Write-Host "==== $m" -ForegroundColor Cyan }

Step '1. Aristotle key and MCP server'
& (Join-Path $Kit 'check_aristotle.ps1')
$chk = $LASTEXITCODE
if ($chk -eq 1) {
    Write-Host 'Aristotle does not accept the key in ARISTOTLE_API_KEY.' -ForegroundColor Yellow
    Write-Host 'Set a valid key as the user environment variable ARISTOTLE_API_KEY, close this window, and double-click continue_round2.cmd again.'
    Stop-Transcript | Out-Null
    return
}
if ($chk -eq 2) {
    Write-Host 'The Aristotle MCP server does not start. Tell Claude. See results\aristotle_check.txt.' -ForegroundColor Yellow
    Stop-Transcript | Out-Null
    return
}
Write-Host 'Aristotle key and MCP server are ready.'

Step '2. Hybrid folder to Lean 4.28.0'
$h = Join-Path $Root 'hybrid\lean_type_sound'
if ((Get-Content (Join-Path $h 'lean-toolchain') -Raw).Trim() -ne 'leanprover/lean4:v4.28.0') {
    foreach ($f in @('lean-toolchain', 'lakefile.lean', 'lake-manifest.json')) {
        Copy-Item (Join-Path $Kit "direct\$f") (Join-Path $h $f) -Force
    }
    Remove-Item (Join-Path $h '.lake\packages'), (Join-Path $h '.lake\build') -Recurse -Force -ErrorAction SilentlyContinue
    $dp = Join-Path $Root 'direct\lean_type_sound\.lake\packages'
    if (Test-Path $dp) {
        robocopy $dp (Join-Path $h '.lake\packages') /E /NFL /NDL /NJH /NJS /NP | Out-Null
        if ($LASTEXITCODE -ge 8) { throw 'robocopy of the Lean 4.28.0 packages failed' }
    }
    git -C (Join-Path $Root 'hybrid') commit -q -am 'Switch to Lean 4.28.0 for Aristotle (proof round 2)'
    Push-Location $h
    try {
        lake build
        if ($LASTEXITCODE -ne 0) { throw 'lake build failed in the Hybrid folder with Lean 4.28.0' }
    } finally { Pop-Location }
    Write-Host 'Hybrid now uses Lean 4.28.0.'
} else { Write-Host 'Hybrid already uses Lean 4.28.0.' }

Step '3. Claude Code setup'
& (Join-Path $Kit 'prep_claude.ps1')

Step '4. Direct (Aristotle) in a second window'
if (Test-Path (Join-Path $res 'direct\project_id.txt')) {
    Write-Host 'Direct was submitted before. Not started again.'
} else {
    Start-Process -FilePath 'powershell' -ArgumentList @('-NoProfile', '-ExecutionPolicy', 'Bypass', '-NoExit', '-File', (Join-Path $Kit 'run_direct.ps1'))
}

Step '5. Second pass, Docs, Hybrid (this takes many hours)'
& (Join-Path $Kit 'run_all.ps1') -Runs @('second-pass', 'docs', 'hybrid')

Step '6. Restore the Claude Code setup and write the result bundle'
& (Join-Path $Kit 'prep_claude.ps1') -Restore
try { & (Join-Path $Kit 'collect_results.ps1') } catch { Write-Host "Bundle not written: $($_.Exception.Message)" }

Step 'Done. Claude reads the results from proof_round2\results.'
Stop-Transcript | Out-Null
