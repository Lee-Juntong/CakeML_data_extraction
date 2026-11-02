# Proof round 2: one start for everything. Double-click start_round2.cmd to run this script.
# 1. Checks the tools and installs uv and aristotlelib if they are missing.
# 2. Makes the five work folders (setup_round2.ps1).
# 3. Prepares Claude Code (prep_claude.ps1).
# 4. Starts Direct in a second window (run_direct.ps1).
# 5. Runs Skills, Second pass, Docs, and Hybrid one after the other (run_all.ps1).
# 6. Restores the Claude Code setup.
# Nothing is pushed. All logs go to proof_round2\results\.
$ErrorActionPreference = 'Stop'
$Kit = 'E:\NUS\mcomp\Dissertation\publication\formalise2027\proof_round2'
$res = Join-Path $Kit 'results'
New-Item -ItemType Directory -Force $res | Out-Null
Start-Transcript -Path (Join-Path $res 'start_round2_transcript.txt') -Append | Out-Null

function Step([string]$m) { Write-Host ''; Write-Host "==== $m" -ForegroundColor Cyan }

Step '1. Tools'
& (Join-Path $Kit 'check_tools.ps1')
$userBin = Join-Path $env:USERPROFILE '.local\bin'
if (-not (Get-Command uv -ErrorAction SilentlyContinue)) {
    Write-Host 'Installing uv (https://astral.sh/uv)'
    powershell -NoProfile -ExecutionPolicy Bypass -Command "irm https://astral.sh/uv/install.ps1 | iex"
    $env:Path = "$userBin;$env:Path"
}
if (-not (Get-Command aristotle -ErrorAction SilentlyContinue)) {
    Write-Host 'Installing aristotlelib'
    uv tool install aristotlelib
    $env:Path = "$userBin;$env:Path"
}
foreach ($t in @('git', 'lake', 'claude', 'uvx', 'aristotle')) {
    if (-not (Get-Command $t -ErrorAction SilentlyContinue)) { throw "The tool '$t' is missing. Install it and start again." }
}
if (-not $env:ARISTOTLE_API_KEY) { throw 'ARISTOTLE_API_KEY is not set. Set it as a user environment variable and start again.' }
& (Join-Path $Kit 'check_tools.ps1')

Step '2. Work folders'
& (Join-Path $Kit 'setup_round2.ps1')

Step '3. Claude Code setup'
& (Join-Path $Kit 'prep_claude.ps1')

Step '4. Direct (Aristotle) in a second window'
Start-Process -FilePath 'powershell' -ArgumentList @('-NoProfile', '-ExecutionPolicy', 'Bypass', '-NoExit', '-File', (Join-Path $Kit 'run_direct.ps1'))

Step '5. Skills, Second pass, Docs, Hybrid (this takes many hours)'
& (Join-Path $Kit 'run_all.ps1')

Step '6. Restore the Claude Code setup'
& (Join-Path $Kit 'prep_claude.ps1') -Restore

Step 'Done. Claude reads the results from proof_round2\results.'
Stop-Transcript | Out-Null
