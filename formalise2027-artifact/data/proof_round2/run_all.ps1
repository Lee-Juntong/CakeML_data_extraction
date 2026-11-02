# Proof round 2: run the four Claude Code workflows one after the other.
#   powershell -ExecutionPolicy Bypass -File <kit>\run_all.ps1
# Optional: -Runs hybrid,docs to run only some of them.
param([string[]]$Runs = @('skills', 'second-pass', 'docs', 'hybrid'))
$Kit = 'E:\NUS\mcomp\Dissertation\publication\formalise2027\proof_round2'
$log = Join-Path $Kit 'results\run_all_log.txt'
New-Item -ItemType Directory -Force (Join-Path $Kit 'results') | Out-Null
foreach ($r in $Runs) {
    Add-Content -Path $log -Value "$(Get-Date -Format 'yyyy-MM-dd HH:mm:ss') start $r"
    $p = Start-Process -FilePath 'powershell' -ArgumentList @('-NoProfile', '-ExecutionPolicy', 'Bypass', '-File', (Join-Path $Kit 'run_headless.ps1'), '-Run', $r) -NoNewWindow -Wait -PassThru
    Add-Content -Path $log -Value "$(Get-Date -Format 'yyyy-MM-dd HH:mm:ss') end $r, exit code $($p.ExitCode)"
    if ($p.ExitCode -ne 0) {
        Add-Content -Path $log -Value "$(Get-Date -Format 'yyyy-MM-dd HH:mm:ss') stopped after an error in $r"
        break
    }
}
Add-Content -Path $log -Value "$(Get-Date -Format 'yyyy-MM-dd HH:mm:ss') run_all finished"
