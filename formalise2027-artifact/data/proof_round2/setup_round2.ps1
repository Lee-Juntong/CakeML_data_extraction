# Proof round 2: make six work folders from the repaired translation de795c9f6.
# Run in Windows PowerShell:
#   powershell -ExecutionPolicy Bypass -File E:\NUS\mcomp\Dissertation\publication\formalise2027\proof_round2\setup_round2.ps1
# The script does not push and does not change your current branch.

$ErrorActionPreference = 'Stop'
$Clone  = 'E:\NUS\mcomp\Dissertation\CML_Proof\cakeml'
$Pub    = 'E:\NUS\mcomp\Dissertation\publication\formalise2027'
$Kit    = Join-Path $Pub 'proof_round2'
$Bundle = Join-Path $Pub 'repair\lean-translate-round5-repair.bundle'
$Root   = 'E:\NUS\mcomp\Dissertation\r2'
$Start  = 'de795c9f6d6515d6c99bdcbb0f8d32e31ee10af6'
$Runs   = @('skills', 'second-pass', 'docs', 'hybrid', 'direct')

function Run([string]$what, [scriptblock]$cmd) {
    Write-Host "== $what"
    & $cmd
    if ($LASTEXITCODE -ne 0) { throw "Failed: $what (exit code $LASTEXITCODE)" }
}

# 1. Check the tools.
foreach ($t in @('git', 'lake', 'elan', 'uvx', 'claude')) {
    if (-not (Get-Command $t -ErrorAction SilentlyContinue)) { throw "Install '$t' first. See README.md, step 1." }
}
if ($env:ARISTOTLE_API_KEY) { Write-Host 'ARISTOTLE_API_KEY: set' } else { throw 'ARISTOTLE_API_KEY is not set in this PowerShell window.' }

# 2. Get the repaired translation from the bundle.
Set-Location $Clone
Run 'git long paths' { git config core.longpaths true }
Run 'verify bundle' { git bundle verify $Bundle }
$have = git rev-parse --verify --quiet lean-translate-round5-repair
if (-not $have) {
    Run 'fetch repair branch from bundle' { git fetch $Bundle lean-translate-round5-repair:lean-translate-round5-repair }
}
$head = (git rev-parse lean-translate-round5-repair).Trim()
if ($head -ne $Start) { throw "lean-translate-round5-repair is at $head. Expected $Start. Tell Claude." }

# 3. Keep the Claude settings folder out of git.
$common = (git rev-parse --git-common-dir).Trim()
if (-not [System.IO.Path]::IsPathRooted($common)) { $common = Join-Path $Clone $common }
$exclude = Join-Path $common 'info\exclude'
if (-not (Test-Path $exclude) -or -not (Select-String -Path $exclude -SimpleMatch '.claude/' -Quiet)) {
    Add-Content -Path $exclude -Value '.claude/'
}

# 4. Make one worktree and one branch per run.
New-Item -ItemType Directory -Force $Root | Out-Null
foreach ($r in $Runs) {
    $dir = Join-Path $Root $r
    $br  = "proof2-$r"
    if (Test-Path $dir) { Write-Host "== $dir exists. Skipped."; continue }
    Run "worktree $r" { git worktree add -b $br $dir $Start }
    $proj = Join-Path $dir 'lean_type_sound'
    if ($r -eq 'direct') {
        foreach ($f in @('lean-toolchain', 'lakefile.lean', 'lake-manifest.json')) {
            Copy-Item (Join-Path $Kit "direct\$f") (Join-Path $proj $f) -Force
        }
        Run 'commit Lean 4.28.0 for Direct' { git -C $dir commit -am 'Switch to Lean 4.28.0 for Aristotle, as in dd68757d7' }
    } else {
        New-Item -ItemType Directory -Force (Join-Path $proj '.claude') | Out-Null
        Copy-Item (Join-Path $Kit 'settings\settings.local.json') (Join-Path $proj '.claude\settings.local.json') -Force
    }
}

# 5. Connect the MCP servers. The scope is local: each folder has its own list.
#    Hybrid gets lean-lsp and Aristotle, as in May. The other runs get lean-lsp only.
#    The Aristotle server reads ARISTOTLE_API_KEY from your environment. The key is not written to any file.
foreach ($r in @('skills', 'second-pass', 'docs', 'hybrid')) {
    $proj = Join-Path (Join-Path $Root $r) 'lean_type_sound'
    Push-Location $proj
    try {
        $list = claude mcp list | Out-String
        if ($list -notmatch 'lean-lsp') { Run "add lean-lsp in $r" { claude mcp add lean-lsp -- uvx lean-lsp-mcp } }
        if ($r -eq 'hybrid' -and $list -notmatch 'aristotle') {
            Run 'add aristotle in hybrid' { claude mcp add aristotle -- uvx --exclude-newer 2026-05-07T00:00:00Z --from git+https://github.com/septract/lean-aristotle-mcp@e53a7ffb856c53d1e85166668af89fe4175a4898 aristotle-mcp }
        }
        Write-Host "== MCP servers in $r"
        $now = claude mcp list | Out-String
        Write-Host $now
        if ($r -ne 'hybrid' -and $now -match 'aristotle') {
            Write-Warning "$r lists an Aristotle server. Remove it (README.md, step 1.6) before the run."
        }
    } finally { Pop-Location }
}

# 6. Build each project once. The first build downloads the packages.
#    The other Lean 4.29.1 folders get a copy of the packages to save time and disk.
$first = Join-Path $Root 'skills\lean_type_sound'
foreach ($r in $Runs) {
    $proj = Join-Path (Join-Path $Root $r) 'lean_type_sound'
    if ($r -ne 'skills' -and $r -ne 'direct' -and -not (Test-Path (Join-Path $proj '.lake\packages'))) {
        Write-Host "== copy packages to $r"
        robocopy (Join-Path $first '.lake\packages') (Join-Path $proj '.lake\packages') /E /NFL /NDL /NJH /NJS /NP | Out-Null
        if ($LASTEXITCODE -ge 8) { throw "robocopy failed for $r" }
    }
    Push-Location $proj
    try {
        if ($r -eq 'direct') {
            Write-Host '== lake build in direct (Lean 4.28.0)'
            lake build
            if ($LASTEXITCODE -ne 0) { Write-Warning 'The Direct build failed. Send Claude the last 40 lines.' }
        } else {
            Run "lake build in $r (warnings about sorry are expected)" { lake build }
        }
    } finally { Pop-Location }
}

Write-Host ''
Write-Host 'Setup is complete. Check the MCP lists above:'
Write-Host '  skills, second-pass, docs: lean-lsp only (no aristotle)'
Write-Host '  hybrid: lean-lsp and aristotle, both connected'
Write-Host 'Then continue with README.md, step 3.'
