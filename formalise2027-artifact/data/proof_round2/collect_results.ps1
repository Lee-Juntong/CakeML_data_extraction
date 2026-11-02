# Proof round 2: put all result branches into one bundle file for Claude.
# Run in Windows PowerShell after the last run:
#   powershell -ExecutionPolicy Bypass -File E:\NUS\mcomp\Dissertation\publication\formalise2027\proof_round2\collect_results.ps1
# The script does not push.

$ErrorActionPreference = 'Stop'
$Clone = 'E:\NUS\mcomp\Dissertation\CML_Proof\cakeml'
$Kit   = 'E:\NUS\mcomp\Dissertation\publication\formalise2027\proof_round2'
$Out   = Join-Path $Kit 'results\proof_round2.bundle'
New-Item -ItemType Directory -Force (Join-Path $Kit 'results') | Out-Null

Set-Location $Clone
$branches = @()
foreach ($r in @('skills', 'second-pass', 'docs', 'hybrid', 'direct')) {
    git rev-parse --verify --quiet "proof2-$r" | Out-Null
    if ($LASTEXITCODE -eq 0) { $branches += "proof2-$r" } else { Write-Warning "Branch proof2-$r does not exist. Skipped." }
}
if ($branches.Count -eq 0) { throw 'No result branch found.' }
git bundle create $Out @branches '^de795c9f6'
if ($LASTEXITCODE -ne 0) { throw 'git bundle create failed.' }
git bundle verify $Out
foreach ($b in $branches) { git log --oneline -1 $b }
Write-Host "Bundle: $Out"
Write-Host 'Tell Claude that the results are ready.'
