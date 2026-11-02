# PrimSemEnv run: submit r2\primsemenv\lean_type_sound to Aristotle with the Direct prompt, wait, download,
# send "continue" on OUT_OF_BUDGET (at most $MaxContinues), download a snapshot after each task.
# Last line of run_log.txt: "PRIMSEMENV DONE: <state>".
param([int]$MaxContinues = 4)
$ErrorActionPreference = 'Continue'
$Kit  = 'E:\NUS\mcomp\Dissertation\publication\formalise2027\proof_round2'
$Root = 'E:\NUS\mcomp\Dissertation\r2'
$proj = Join-Path $Root 'primsemenv\lean_type_sound'
$out  = Join-Path $Kit 'results\primsemenv'
New-Item -ItemType Directory -Force $out | Out-Null
$log  = Join-Path $out 'run_log.txt'
function Log([string]$m) { $line = "$(Get-Date -Format 'yyyy-MM-dd HH:mm:ss') $m"; Add-Content -Path $log -Value $line -Encoding UTF8; Write-Host $line }
function Ari { & uvx --from aristotlelib@latest aristotle @args 2>&1 | ForEach-Object { "$_" } }
$env:PYTHONIOENCODING = 'utf-8'
$env:PYTHONUTF8 = '1'
if (-not $env:ARISTOTLE_API_KEY) { $env:ARISTOTLE_API_KEY = [Environment]::GetEnvironmentVariable('ARISTOTLE_API_KEY', 'User') }
if (-not $env:ARISTOTLE_API_KEY) { Log 'PRIMSEMENV DONE: ARISTOTLE_API_KEY is not set'; return }
Log ("aristotle version: " + ((Ari --version) -join ' '))
$prompt = 'Fill in all sorries of the theorems'
$prompt | Set-Content (Join-Path $out 'prompt_used.txt') -Encoding UTF8

$idFile = Join-Path $out 'project_id.txt'
if (Test-Path $idFile) {
    $id = (Get-Content $idFile -Raw).Trim()
    Log "project $id was submitted before. Skipping the submission."
} else {
    Set-Location $proj
    Log 'submission started'
    Ari submit $prompt --project-dir . | Tee-Object -FilePath (Join-Path $out 'submit_output.txt')
    $text = Get-Content (Join-Path $out 'submit_output.txt') -Raw
    $m = [regex]::Match($text, '([0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12})')
    if (-not $m.Success) { Log 'PRIMSEMENV DONE: no project id in the submit output'; return }
    $id = $m.Groups[1].Value
    Set-Content $idFile $id -Encoding UTF8
    Log "project id $id"
}

function TaskLines { @((Ari tasks $id | Out-String) -split "`n" | Where-Object { $_ -match '^[0-9a-fA-F]{8}-' }) }
$sent = @(TaskLines | Where-Object { $_ -match '\scontinue\s' }).Count
while ($true) {
    $lines = TaskLines
    if ($lines.Count -eq 0) { Start-Sleep -Seconds 120; continue }
    if (($lines -join "`n") -match 'IN_PROGRESS|QUEUED|RUNNING|PENDING') { Start-Sleep -Seconds 300; continue }
    $latest = $lines[0].Trim()
    $state = ($latest -split '\s+')[-1]
    $stage = $lines.Count
    Log "task finished: $latest"
    $tgz = Join-Path $Root "primsemenv_stage$stage.tar.gz"
    Ari download $id --destination $tgz | Out-File (Join-Path $out "download_stage$stage.txt") -Encoding UTF8
    $dest = Join-Path $Root "primsemenv_stage$stage"
    New-Item -ItemType Directory -Force $dest | Out-Null
    tar -xzf $tgz -C $dest
    Log "snapshot of stage $stage unpacked in $dest"
    if ($state -ne 'OUT_OF_BUDGET') { Log "PRIMSEMENV DONE: $state after $stage task(s)"; break }
    if ($sent -ge $MaxContinues) { Log "PRIMSEMENV DONE: OUT_OF_BUDGET, limit of $MaxContinues continuations reached"; break }
    $before = $lines.Count
    Ari continue $id 'continue' | Out-File (Join-Path $out "continue$($sent + 1)_output.txt") -Encoding UTF8
    $sent++
    Log "continuation $sent sent"
    for ($i = 0; $i -lt 30 -and (TaskLines).Count -le $before; $i++) { Start-Sleep -Seconds 20 }
}
