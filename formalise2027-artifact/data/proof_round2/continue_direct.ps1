# Proof round 2: Direct continuation loop. In May, task 2cf818c7 stopped at OUT_OF_BUDGET and one continuation
# (task 1a8c0cd4) followed. Here, on the user's request (2026-10-12), the script sends "continue" each time a task
# stops at OUT_OF_BUDGET, until a task ends in another state or $MaxContinues is reached. No model polls; this script waits.
# After each task it downloads a snapshot to r2\direct_stage<N>. The last line of run_log.txt is "DIRECT DONE: <state>".
#   powershell -ExecutionPolicy Bypass -File <kit>\continue_direct.ps1
param([int]$MaxContinues = 8)
$ErrorActionPreference = 'Continue'
$Kit  = 'E:\NUS\mcomp\Dissertation\publication\formalise2027\proof_round2'
$Root = 'E:\NUS\mcomp\Dissertation\r2'
$out  = Join-Path $Kit 'results\direct'
$log  = Join-Path $out 'run_log.txt'
function Log([string]$m) { $line = "$(Get-Date -Format 'yyyy-MM-dd HH:mm:ss') $m"; Add-Content -Path $log -Value $line -Encoding UTF8; Write-Host $line }
function Ari { & uvx --from aristotlelib@latest aristotle @args 2>&1 | ForEach-Object { "$_" } }
$env:PYTHONIOENCODING = 'utf-8'
$env:PYTHONUTF8 = '1'
if (-not $env:ARISTOTLE_API_KEY) { Log 'DIRECT DONE: ARISTOTLE_API_KEY is not set in this window'; return }

$id = (Get-Content (Join-Path $out 'project_id.txt') -Raw).Trim()
function TaskLines { @((Ari tasks $id | Out-String) -split "`n" | Where-Object { $_ -match '^[0-9a-fA-F]{8}-' }) }

# Continuations already sent (task name "continue").
$sent = @(TaskLines | Where-Object { $_ -match '\scontinue\s' }).Count
Log "continuation loop started for project $id ($sent continuation(s) sent before, at most $MaxContinues)"

while ($true) {
    $lines = TaskLines
    if ($lines.Count -eq 0) { Log 'task list empty or not readable; trying again in 10 minutes'; Start-Sleep -Seconds 600; continue }
    if (($lines -join "`n") -match 'IN_PROGRESS|QUEUED|RUNNING|PENDING') { Start-Sleep -Seconds 600; continue }

    $latest = $lines[0].Trim()
    $state = ($latest -split '\s+')[-1]
    $stage = $lines.Count
    Log "task finished: $latest"

    $tgz = Join-Path $Root "direct_stage$stage.tar.gz"
    Ari download $id --destination $tgz | Out-File (Join-Path $out "download_stage$stage.txt") -Encoding UTF8
    $dest = Join-Path $Root "direct_stage$stage"
    New-Item -ItemType Directory -Force $dest | Out-Null
    tar -xzf $tgz -C $dest
    Log "snapshot of stage $stage unpacked in $dest"

    if ($state -ne 'OUT_OF_BUDGET') { Log "DIRECT DONE: $state after $stage task(s)"; break }
    if ($sent -ge $MaxContinues) { Log "DIRECT DONE: OUT_OF_BUDGET, limit of $MaxContinues continuations reached"; break }

    $before = $lines.Count
    Ari continue $id 'continue' | Out-File (Join-Path $out "continue$($sent + 1)_output.txt") -Encoding UTF8
    $sent++
    Log "continuation $sent sent"
    # Wait until the new task shows in the list.
    for ($i = 0; $i -lt 30 -and (TaskLines).Count -le $before; $i++) { Start-Sleep -Seconds 20 }
}
