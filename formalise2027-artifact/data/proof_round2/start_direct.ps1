# Proof round 2: check the Aristotle key, then run Direct. Double-click start_direct.cmd.
$Kit = 'E:\NUS\mcomp\Dissertation\publication\formalise2027\proof_round2'
& (Join-Path $Kit 'check_aristotle.ps1')
if ($LASTEXITCODE -ne 0) {
    Write-Host ''
    Write-Host 'Aristotle does not accept the key in ARISTOTLE_API_KEY.' -ForegroundColor Yellow
    Write-Host '1. Open https://aristotle.harmonic.fun/dashboard/keys and create a new key.'
    Write-Host '2. Set it as the user environment variable ARISTOTLE_API_KEY (Windows: Edit environment variables for your account).'
    Write-Host '3. Close this window and double-click start_direct.cmd again.'
    return
}
& (Join-Path $Kit 'run_direct.ps1')
