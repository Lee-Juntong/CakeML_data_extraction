# Proof round 2: prepare Claude Code on this computer, and undo it after the runs.
#   powershell -ExecutionPolicy Bypass -File <kit>\prep_claude.ps1           (before the runs)
#   powershell -ExecutionPolicy Bypass -File <kit>\prep_claude.ps1 -Restore  (after the runs)
param([switch]$Restore)
$Kit   = 'E:\NUS\mcomp\Dissertation\publication\formalise2027\proof_round2'
$state = Join-Path $Kit 'results\claude_setup'
New-Item -ItemType Directory -Force $state | Out-Null
$global = Join-Path $env:USERPROFILE '.claude\CLAUDE.md'
$backup = Join-Path $env:USERPROFILE '.claude\CLAUDE.md.round2-backup'
$disabledFile = Join-Path $state 'plugins_disabled_by_prep.txt'

if ($Restore) {
    if (Test-Path $backup) { Move-Item $backup $global; Write-Host 'Global CLAUDE.md restored.' }
    if (Test-Path $disabledFile) {
        Get-Content $disabledFile | Where-Object { $_ } | ForEach-Object { claude plugin enable $_ }
        Write-Host 'Plugins enabled again.'
    }
    return
}

claude --version | Out-File (Join-Path $state 'claude_version.txt') -Encoding utf8
claude plugin list | Out-File (Join-Path $state 'plugins_before.txt') -Encoding utf8

# 1. Install the lean4 plugin (lean4-skills), as in May.
claude plugin marketplace add cameronfreer/lean4-skills
claude plugin install lean4@lean4-skills

# 2. Disable the other enabled plugins for the time of the runs.
$listing = claude plugin list | Out-String
$names = [regex]::Matches($listing, '([A-Za-z0-9_.-]+@[A-Za-z0-9_.-]+)') | ForEach-Object { $_.Groups[1].Value } | Sort-Object -Unique
$toDisable = @($names | Where-Object { $_ -notlike 'lean4@*' })
$toDisable | Set-Content $disabledFile -Encoding utf8
foreach ($n in $toDisable) { claude plugin disable $n }

# 3. Move the global CLAUDE.md away for the time of the runs.
if (Test-Path $global) { Move-Item $global $backup; Write-Host 'Global CLAUDE.md moved away.' }

claude plugin list | Out-File (Join-Path $state 'plugins_during_runs.txt') -Encoding utf8
Write-Host 'Claude Code is ready for the runs.'
