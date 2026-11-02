# Docs run only: check whether the agent changed an existing def into a partial def.
# Run in a second PowerShell window after the first summary of the Docs run:
#   powershell -ExecutionPolicy Bypass -File E:\NUS\mcomp\Dissertation\publication\formalise2027\proof_round2\check_partial.ps1

$dir = 'E:\NUS\mcomp\Dissertation\r2\docs'
$start = 'de795c9f6d6515d6c99bdcbb0f8d32e31ee10af6'
$diff = git -C $dir diff $start -- '*.lean'
$mods = '(?:(?:private|protected|noncomputable|unsafe)\s+)*'
$added = @($diff | Select-String "^\+\s*$($mods)partial\s+def\s+([^\s:({\[]+)" | ForEach-Object { $_.Matches[0].Groups[1].Value })
$removed = @($diff | Select-String "^-\s*$($mods)def\s+([^\s:({\[]+)" | ForEach-Object { $_.Matches[0].Groups[1].Value })
$changed = @($added | Where-Object { $removed -contains $_ } | Sort-Object -Unique)
if ($changed.Count -gt 0) {
    Write-Host 'The agent changed these definitions from def to partial def:'
    $changed | ForEach-Object { Write-Host "  $_" }
    Write-Host 'Send prompts\docs_message2_only_if_partial.txt. Write this in RUN_LOG.md.'
} else {
    Write-Host 'No def was changed into partial def. Do not send message 2. Send prompts\docs_message3.txt.'
}
