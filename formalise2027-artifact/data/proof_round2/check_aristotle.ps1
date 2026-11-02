# Proof round 2: set up and check Aristotle. Writes results\aristotle_check.txt. The key value is never written.
# 1. Checks the key with the latest Aristotle client.
# 2. Registers the Aristotle MCP server in the Hybrid folder with the package versions of 7 May 2026
#    (uv --exclude-newer). Newer packages (mcp 2.x) make this server stop at start.
# 3. Starts the server once to check it.
# Exit code: 0 = all good, 1 = key not accepted, 2 = MCP server does not start.
$ErrorActionPreference = 'Continue'
$Kit = 'E:\NUS\mcomp\Dissertation\publication\formalise2027\proof_round2'
$out = Join-Path $Kit 'results\aristotle_check.txt'
New-Item -ItemType Directory -Force (Split-Path $out) | Out-Null
function Clean($s) { ($s | Out-String) -replace 'arstl_[A-Za-z0-9_\-]+', '[KEY]' }
$mcpArgs = @('--exclude-newer', '2026-05-07T00:00:00Z', '--from',
             'git+https://github.com/septract/lean-aristotle-mcp@e53a7ffb856c53d1e85166668af89fe4175a4898', 'aristotle-mcp')
$k = $env:ARISTOTLE_API_KEY
$L = @("date: $(Get-Date -Format s)")
if ($k) { $L += "key: set, length $($k.Length)" } else { $L += 'key: missing' }

$L += '--- latest client: list'
$latest = Clean (& uvx --from aristotlelib@latest aristotle list --limit 1 2>&1)
$latestOk = ($LASTEXITCODE -eq 0) -and ($latest -notmatch '(?i)invalid api key')
$L += $latest
$L += "latest client accepts the key: $latestOk"

$L += '--- register the Aristotle MCP server in the Hybrid folder'
Push-Location 'E:\NUS\mcomp\Dissertation\r2\hybrid\lean_type_sound'
$L += Clean (& claude mcp remove aristotle -s local 2>&1)
$L += Clean (& claude mcp add aristotle -- uvx @mcpArgs 2>&1)
Pop-Location

$L += '--- Aristotle MCP server start (stdin closed, 180 s limit)'
$errf = Join-Path $env:TEMP 'aristotle_mcp_err.txt'
$outf = Join-Path $env:TEMP 'aristotle_mcp_out.txt'
Remove-Item $errf, $outf -ErrorAction SilentlyContinue
$cmdline = 'uvx ' + ($mcpArgs -join ' ') + " < NUL > `"$outf`" 2> `"$errf`""
$p = Start-Process -FilePath 'cmd.exe' -ArgumentList @('/c', $cmdline) -NoNewWindow -PassThru
if (-not $p.WaitForExit(180000)) { try { $p.Kill() } catch {}; $L += 'server still running after 180 s' } else { $L += "server exit code $($p.ExitCode)" }
$errText = ''
if (Test-Path $errf) { $errText = Get-Content $errf -Raw; $L += Clean $errText }
$mcpOk = $errText -match 'Aristotle MCP server starting'
$L += "MCP server starts: $mcpOk"

$L += '--- claude mcp get aristotle (Hybrid folder)'
Push-Location 'E:\NUS\mcomp\Dissertation\r2\hybrid\lean_type_sound'
$L += Clean (& claude mcp get aristotle 2>&1)
Pop-Location
$L | Set-Content -Path $out -Encoding UTF8
Write-Host "Check written to $out"
if (-not $latestOk) { exit 1 }
if (-not $mcpOk) { exit 2 }
exit 0
