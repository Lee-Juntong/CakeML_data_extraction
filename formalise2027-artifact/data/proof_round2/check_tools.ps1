# Proof round 2: write the versions of the tools to results\tools_check.txt. The key value is never written.
$ErrorActionPreference = 'Continue'
$out = 'E:\NUS\mcomp\Dissertation\publication\formalise2027\proof_round2\results\tools_check.txt'
New-Item -ItemType Directory -Force (Split-Path $out) | Out-Null
$lines = @("date: $(Get-Date -Format s)", "os: $([Environment]::OSVersion.VersionString)", "cores: $([Environment]::ProcessorCount)")
try { $mem = (Get-CimInstance Win32_ComputerSystem).TotalPhysicalMemory; $lines += "ram_gb: $([math]::Round($mem/1GB,1))" } catch {}
try { $d = Get-PSDrive E; $lines += "E_free_gb: $([math]::Round($d.Free/1GB,1))" } catch {}
foreach ($t in @('git','lake','elan','lean','uv','uvx','claude','aristotle','python','tar','bash')) {
  $c = Get-Command $t -ErrorAction SilentlyContinue
  if ($c) {
    $v = ''
    try { $v = (& $t --version 2>&1 | Select-Object -First 1) -join ' ' } catch { $v = 'version failed' }
    $lines += "${t}: $($c.Source) | $v"
  } else { $lines += "${t}: MISSING" }
}
$lines += "ARISTOTLE_API_KEY: $(if ($env:ARISTOTLE_API_KEY) {'set'} else {'missing'})"
$lines += "ANTHROPIC_API_KEY: $(if ($env:ANTHROPIC_API_KEY) {'set (the run scripts remove it)'} else {'not set'})"
$lines += "global CLAUDE.md: $(Test-Path (Join-Path $env:USERPROFILE '.claude\CLAUDE.md'))"
try { $lines += 'claude --help has --effort: ' + [string](((& claude --help 2>&1) -join "`n") -match '--effort') } catch {}
try { $lines += "claude plugins:"; $lines += (claude plugin list 2>&1 | Out-String) } catch { $lines += "plugin list failed" }
try { $lines += "claude mcp (user):"; Push-Location $env:USERPROFILE; $lines += (claude mcp list 2>&1 | Out-String); Pop-Location } catch { $lines += "mcp list failed" }
$lines | Set-Content -Path $out -Encoding UTF8
Write-Host "Tool check written to $out"
