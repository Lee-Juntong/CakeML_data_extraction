# Proof round 2: Direct run. Submit the whole project to Aristotle, wait, and download the result.
#   powershell -ExecutionPolicy Bypass -File <kit>\run_direct.ps1
$ErrorActionPreference = 'Stop'
$Kit  = 'E:\NUS\mcomp\Dissertation\publication\formalise2027\proof_round2'
$Root = 'E:\NUS\mcomp\Dissertation\r2'
$proj = Join-Path $Root 'direct\lean_type_sound'
$out  = Join-Path $Kit 'results\direct'
New-Item -ItemType Directory -Force $out | Out-Null
$log = Join-Path $out 'run_log.txt'
function Log([string]$m) { $line = "$(Get-Date -Format 'yyyy-MM-dd HH:mm:ss') $m"; Add-Content -Path $log -Value $line -Encoding UTF8; Write-Host $line }

if (-not $env:ARISTOTLE_API_KEY) { throw 'ARISTOTLE_API_KEY is not set in this window.' }
# Use the latest Aristotle client. The installed client (aristotlelib 1.0.1) is from May.
function Ari { & uvx --from aristotlelib@latest aristotle @args }
# The client prints progress bars with characters that the GBK console cannot encode. Without UTF-8, --wait stops with an error.
$env:PYTHONIOENCODING = 'utf-8'
$env:PYTHONUTF8 = '1'
$ErrorActionPreference = 'Continue'
Log ("aristotle version: " + ((Ari --version 2>&1) -join ' '))
$ErrorActionPreference = 'Stop'

# 1. Prompt: the May prompt if the PowerShell history has it, else the prompt that Claude wrote.
$prompt = $null
try {
    $hist = (Get-PSReadLineOption).HistorySavePath
    if (Test-Path $hist) {
        $all = Select-String -Path $hist -Pattern 'aristotle submit\s+"([^"]+)"' | ForEach-Object { $_.Matches[0].Groups[1].Value }
        $all | Set-Content (Join-Path $out 'may_prompt_candidates.txt') -Encoding UTF8
        # The key tests of October submitted "Prove that the square root of 2 is irrational". That is not a May prompt.
        $cands = @($all | Where-Object { $_ -notmatch 'square root of 2' })
        if ($cands) {
            $prompt = @($cands)[-1]
            Log 'prompt: the last May prompt found in the PowerShell history'
        }
    }
} catch { Log "history check failed: $($_.Exception.Message)" }
if (-not $prompt) {
    $prompt = (Get-Content (Join-Path $Kit 'direct\aristotle_prompt.txt') -Raw -Encoding UTF8).Trim()
    Log 'prompt: direct\aristotle_prompt.txt (written by Claude; the May prompt was not found)'
}
$prompt | Set-Content (Join-Path $out 'prompt_used.txt') -Encoding UTF8

# 2. Submit and wait. A project ID from an earlier submission is reused.
Set-Location $proj
$ErrorActionPreference = 'Continue'
$idFile = Join-Path $out 'project_id.txt'
if (Test-Path $idFile) {
    $id = (Get-Content $idFile -Raw).Trim()
    Log "project $id was submitted before. Skipping the submission."
} else {
    Log 'submission started'
    $arg = $prompt -replace '"', '\"'
    Ari submit $arg --project-dir . --wait 2>&1 | Tee-Object -FilePath (Join-Path $out 'submit_output.txt')
    Log "submission ended, exit $LASTEXITCODE"
    $text = Get-Content (Join-Path $out 'submit_output.txt') -Raw
    $m = [regex]::Match($text, 'Project created:\s*([0-9a-fA-F-]{36})')
    if (-not $m.Success) { $m = [regex]::Match($text, '([0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12})') }
    if (-not $m.Success) { throw 'No project ID in the output. Run: aristotle list --limit 5' }
    $id = $m.Groups[1].Value
    Set-Content $idFile $id -Encoding UTF8
    Log "project id $id"
}

# 3. Wait until no task of the project is queued or in progress. Do not download a partial project.
while ($true) {
    $t = (Ari tasks $id 2>&1 | Out-String)
    if ($t -notmatch '[0-9a-fA-F]{8}-') { Log 'task list empty or not readable; trying again in 10 minutes'; Start-Sleep -Seconds 600; continue }
    if ($t -match 'IN_PROGRESS|QUEUED|RUNNING|PENDING') { Start-Sleep -Seconds 600; continue }
    $st = ($t -split "`n" | Where-Object { $_ -match '[0-9a-fA-F]{8}-' } | Select-Object -First 1).Trim()
    Log "task finished: $st"
    break
}

# 4. Download and unpack the result.
$tgz = Join-Path $Root 'direct_result.tar.gz'
Ari download $id --destination $tgz 2>&1 | Tee-Object -FilePath (Join-Path $out 'download_output.txt')
$dest = Join-Path $Root 'direct_result'
New-Item -ItemType Directory -Force $dest | Out-Null
tar -xzf $tgz -C $dest
Log "result unpacked in $dest. Claude applies it to the proof2-direct branch."
