# Proof round 2: run one Claude Code workflow without a person at the keyboard.
# The script sends the May messages of the run, in sequence, to headless Claude Code
# (claude -p) with Opus 4.7 and effort xhigh. After each message it commits a snapshot.
# It keeps its progress in results\<run>\state.json, so a new start continues where it stopped.
# If a usage limit stops a message, the script waits until the limit resets and then sends
# "continue" to the same session. Each such resume is logged. At the end it runs finish_run.ps1.
# It does not push.
#   powershell -ExecutionPolicy Bypass -File <kit>\run_headless.ps1 -Run skills

param(
    [Parameter(Mandatory = $true)]
    [ValidateSet('skills', 'second-pass', 'docs', 'hybrid')]
    [string]$Run
)
$ErrorActionPreference = 'Stop'
$Kit   = 'E:\NUS\mcomp\Dissertation\publication\formalise2027\proof_round2'
$Root  = 'E:\NUS\mcomp\Dissertation\r2'
$Start = 'de795c9f6d6515d6c99bdcbb0f8d32e31ee10af6'
$dir   = Join-Path $Root $Run
$proj  = Join-Path $dir 'lean_type_sound'
$out   = Join-Path $Kit "results\$Run"
$P     = Join-Path $Kit 'prompts'
New-Item -ItemType Directory -Force $out | Out-Null
$log       = Join-Path $out 'run_log.txt'
$stateFile = Join-Path $out 'state.json'

function Log([string]$m) {
    $line = "$(Get-Date -Format 'yyyy-MM-dd HH:mm:ss') $m"
    Add-Content -Path $log -Value $line -Encoding UTF8
    Write-Host $line
}

# Use the Claude subscription login only. Without these variables, Claude Code cannot bill API credits.
foreach ($v in @('ANTHROPIC_API_KEY', 'ANTHROPIC_AUTH_TOKEN', 'CLAUDE_CODE_USE_BEDROCK', 'CLAUDE_CODE_USE_VERTEX')) {
    Remove-Item "Env:$v" -ErrorAction SilentlyContinue
}
# Only Hybrid may reach Aristotle, as in May.
if ($Run -ne 'hybrid') { Remove-Item Env:ARISTOTLE_API_KEY -ErrorAction SilentlyContinue }
if ($Run -eq 'hybrid' -and -not $env:ARISTOTLE_API_KEY) { throw 'ARISTOTLE_API_KEY is not set in this window.' }

$utf8 = New-Object System.Text.UTF8Encoding $false
$OutputEncoding = $utf8
[Console]::OutputEncoding = $utf8
$common = @('-p', '--model', 'claude-opus-4-7', '--permission-mode', 'acceptEdits',
            '--output-format', 'stream-json', '--verbose')
$help = (& claude --help) -join "`n"
if ($help -match '--effort') { $common += @('--effort', 'xhigh') } else { $env:CLAUDE_CODE_EFFORT_LEVEL = 'xhigh' }

Set-Location $proj
Log "run $Run in $proj"
Log ("arguments: " + ($common -join ' '))
Log ("claude version: " + ((& claude --version) -join ' '))

# Progress state.
$state = [ordered]@{ session = $null; completed = @(); skipped = @(); pending = $null; finished = $false }
if (Test-Path $stateFile) {
    $s = Get-Content $stateFile -Raw -Encoding UTF8 | ConvertFrom-Json
    $state.session = $s.session; $state.pending = $s.pending; $state.finished = [bool]$s.finished
    $state.completed = @($s.completed); $state.skipped = @($s.skipped)
    Log ("state loaded: session $($state.session), completed [$($state.completed -join ',')], skipped [$($state.skipped -join ',')], pending $($state.pending)")
}
function SaveState { $state | ConvertTo-Json | Set-Content $stateFile -Encoding UTF8 }
if ($state.finished) { Log "run $Run is already finished"; return }

function Snapshot([int]$n) {
    git -C $dir add -A | Out-Null
    git -C $dir commit -q -m "Proof round 2: $Run, state after message $n" | Out-Null
    Log ("snapshot after message ${n}: " + ((git -C $dir log --oneline -1) -join ' '))
}

# Send one text to Claude Code. Returns an object with the session, the error flag, and the limit reset time.
function Invoke-Claude([string]$text, [string]$sid, [string]$jf) {
    $a = $common
    if ($sid) { $a = $a + @('--resume', $sid) }
    $text | & claude @a | Out-File -FilePath $jf -Encoding utf8
    $code = $LASTEXITCODE
    $lines = @(Get-Content $jf -Encoding UTF8)
    $init  = $lines | Where-Object { $_ -match '"subtype":"init"' } | Select-Object -First 1
    $res   = $lines | Where-Object { $_ -match '"type":"result"' } | Select-Object -Last 1
    $rl    = $lines | Where-Object { $_ -match '"type":"rate_limit_event"' -and $_ -match '"status":"rejected"' } | Select-Object -Last 1
    $o = [ordered]@{ session = $sid; isError = $true; limited = $false; resetsAt = $null; text = ''; turns = $null; cost = $null; code = $code }
    if ($init) { $o.session = ($init | ConvertFrom-Json).session_id }
    if ($res) {
        $r = $res | ConvertFrom-Json
        $o.isError = [bool]$r.is_error; $o.text = [string]$r.result; $o.turns = $r.num_turns; $o.cost = $r.total_cost_usd
        if ($r.session_id) { $o.session = $r.session_id }
    }
    if ($rl) {
        $o.limited = $true
        try { $o.resetsAt = [int64](($rl | ConvertFrom-Json).rate_limit_info.resetsAt) } catch {}
    }
    if ($o.isError -and $o.text -match '(?i)limit') { $o.limited = $true }
    return $o
}

function Wait-Reset($o) {
    $now = [DateTimeOffset]::UtcNow.ToUnixTimeSeconds()
    if ($o.resetsAt) { $secs = [int64]$o.resetsAt - $now + 120 } else { $secs = 1800 }
    if ($secs -lt 60) { $secs = 60 }
    $at = (Get-Date).AddSeconds($secs).ToString('yyyy-MM-dd HH:mm:ss')
    Log "usage limit reached ($($o.text)). Waiting until $at."
    Start-Sleep -Seconds $secs
}

# Run message n to completion: first the message text (unless resuming), then "continue" after each stop.
function Complete([int]$n, [string]$file, [string]$sid, [bool]$resume) {
    $k = 0; $otherErrors = 0
    if ($resume) {
        $o = [ordered]@{ isError = $true; limited = $true; resetsAt = $null; text = 'resuming an interrupted message'; session = $sid }
        Log "message $n was interrupted before. Resuming session $sid."
    } else {
        $text = Get-Content (Join-Path $P $file) -Raw -Encoding UTF8
        $state.pending = $n; SaveState
        Log "message $n ($file) sent"
        $o = Invoke-Claude $text $sid (Join-Path $out ("message{0}.jsonl" -f $n))
        $sid = $o.session; $state.session = $sid; SaveState
        Log "message $n result: is_error $($o.isError), turns $($o.turns), cost_usd $($o.cost), session $sid, text: $($o.text)"
    }
    while ($o.isError) {
        if ($o.limited) {
            if (-not $resume -or $k -gt 0) { Wait-Reset $o }
        } else {
            $otherErrors++
            if ($otherErrors -gt 3) { Snapshot $n; throw "Message $n failed $otherErrors times. See the jsonl files in $out." }
            Log "message $n stopped with an error ($($o.text)). Waiting 5 minutes."
            Start-Sleep -Seconds 300
        }
        $k++
        Log "intervention: message $n, resume $k, sent 'continue' to session $sid"
        $o = Invoke-Claude 'continue' $sid (Join-Path $out ("message{0}_continue{1}.jsonl" -f $n, $k))
        if ($o.session) { $sid = $o.session; $state.session = $sid; SaveState }
        Log "message $n resume $k result: is_error $($o.isError), turns $($o.turns), cost_usd $($o.cost), text: $($o.text)"
    }
    Snapshot $n
    $state.completed = @($state.completed) + $n; $state.pending = $null; SaveState
    return $sid
}

function ChangedToPartial {
    $diff = git -C $dir diff $Start -- '*.lean'
    $mods = '(?:(?:private|protected|noncomputable|unsafe)\s+)*'
    $added = @($diff | Select-String "^\+\s*$($mods)partial\s+def\s+([^\s:({\[]+)" | ForEach-Object { $_.Matches[0].Groups[1].Value })
    $removed = @($diff | Select-String "^-\s*$($mods)def\s+([^\s:({\[]+)" | ForEach-Object { $_.Matches[0].Groups[1].Value })
    return @($added | Where-Object { $removed -contains $_ } | Sort-Object -Unique)
}

# Hybrid: the Aristotle MCP server must be connected before the first message.
if ($Run -eq 'hybrid' -and -not $state.session) {
    $ok = $false
    for ($i = 1; $i -le 3 -and -not $ok; $i++) {
        $mcp = (& claude mcp list 2>&1 | Out-String)
        Log ("mcp list (try $i): " + (($mcp -split "`n" | Where-Object { $_ -match 'aristotle|lean-lsp' }) -join ' | '))
        if ($mcp -match 'aristotle:[^\r\n]*Connected') { $ok = $true } else { Start-Sleep -Seconds 60 }
    }
    if (-not $ok) { throw 'The Aristotle MCP server does not connect in the Hybrid folder. See results\aristotle_check.txt.' }
}

$steps = switch ($Run) {
    'skills'      { @(@{ n = 1; f = 'skills_message1.txt' }) }
    'second-pass' { @(@{ n = 1; f = 'skills_message1.txt' }, @{ n = 2; f = 'second_pass_message2.txt' }) }
    'docs'        { @(@{ n = 1; f = 'docs_message1.txt' }, @{ n = 2; f = 'docs_message2_only_if_partial.txt' }, @{ n = 3; f = 'docs_message3.txt' }) }
    'hybrid'      { @(@{ n = 1; f = 'hybrid_message1.txt' }, @{ n = 2; f = 'hybrid_message2.txt' }) }
}

$sid = $state.session
foreach ($st in $steps) {
    $n = $st.n
    if (@($state.completed) -contains $n -or @($state.skipped) -contains $n) { continue }
    if ($Run -eq 'docs' -and $n -eq 2 -and $state.pending -ne 2) {
        $changed = ChangedToPartial
        if ($changed.Count -eq 0) {
            Log 'no def changed into partial def. Correction not sent.'
            $state.skipped = @($state.skipped) + 2; SaveState
            continue
        }
        Log ("def changed into partial def: " + ($changed -join ', ') + ". Sending the correction.")
    }
    $resume = ($state.pending -eq $n -and $sid)
    $sid = Complete $n $st.f $sid $resume
}

$state.finished = $true; SaveState
Log 'all messages done. Running finish_run.ps1.'
& (Join-Path $Kit 'finish_run.ps1') -Run $Run
Log "run $Run finished"
