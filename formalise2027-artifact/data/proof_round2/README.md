# Proof round 2: run kit

This kit runs the five proving workflows of May again on the repaired translation (commit `de795c9f6`, branch `lean-translate-round5-repair`). Each run starts from the same commit and keeps its result on its own branch. Nothing is pushed.

## One-click start

Double-click `start_round2.cmd` in this folder. Keep its window open. It runs for many hours and does all steps below without a person at the keyboard:

1. It checks the tools (`results\tools_check.txt`) and installs uv and aristotlelib if they are missing.
2. It makes the five work folders (step 2).
3. It installs the lean4 plugin, disables your other Claude Code plugins, and moves the global `CLAUDE.md` away. At the end it undoes this.
4. It starts Direct in a second window (`run_direct.ps1`).
5. It runs Skills, Second pass, Docs, and Hybrid one after the other with headless Claude Code (`run_all.ps1`, `run_headless.ps1`): Opus 4.7, effort xhigh, the May messages, a snapshot commit after each message. Shell commands outside the allowlist in `settings\settings.local.json` are refused and logged.

Claude reads the logs in `results\` from your folder while the runs go on. Do not use the work folders under `E:\NUS\mcomp\Dissertation\r2` during the runs. The manual steps below are the same procedure by hand.

## The five runs

| Run | Folder | Messages to send, in this sequence | MCP servers |
|---|---|---|---|
| Skills | `E:\NUS\mcomp\Dissertation\r2\skills` | 1. `prompts\skills_message1.txt` | lean-lsp |
| Second pass | `...\r2\second-pass` | 1. `prompts\skills_message1.txt` 2. `prompts\second_pass_message2.txt` | lean-lsp |
| Docs | `...\r2\docs` | 1. `prompts\docs_message1.txt` 2. `prompts\docs_message2_only_if_partial.txt` (only if `check_partial.ps1` finds a def that the agent changed into `partial def`) 3. `prompts\docs_message3.txt` | lean-lsp |
| Hybrid | `...\r2\hybrid` | 1. `prompts\hybrid_message1.txt` 2. `prompts\hybrid_message2.txt` | lean-lsp and aristotle |
| Direct | `...\r2\direct` | Aristotle submission (step 5) | none |

In May, the Aristotle MCP server was connected only for Hybrid. Skills, Second pass, and Docs ran before it was added. In May, the Hybrid agent made no Aristotle call. In round 2, record whether it calls Aristotle.

The prompt files contain the words of the May messages, taken from the logs in `claude-logs`. The line breaks of the terminal export are removed. In May, message 1 of Second pass was pasted from the Skills log and had extra line breaks in the middle of sentences. The words are the same. `prompts\reference_only_docs_reverted_first_session.txt` is for reference only. Do not send it. In May the operator reverted that session.

## Differences from May

Write these differences in `RUN_LOG.md`. The paper reports them.

- May: Joe's Linux computer, Claude Code 2.1.123 to 2.1.132, Claude Team account. Now: your Windows computer, a newer Claude Code, your account.
- May: lean4 plugin, lean-lsp-mcp, and lean-aristotle-mcp of May 2026. Now: the current versions.
- Effort: xhigh in all runs, as in May.
- Direct: only the last words of the May prompt are known. Use the May prompt if step 5.1 finds it. If not, use the prompt in `direct\aristotle_prompt.txt`, which Claude wrote.

## Step 1. Check the tools (one time)

Open Windows PowerShell and do these checks:

1. `git --version`, `elan --version`, `lake --version`, `uv --version`, `claude --version`. If a command is not found, install that tool:
   - uv: `powershell -ExecutionPolicy Bypass -c "irm https://astral.sh/uv/install.ps1 | iex"`
   - Claude Code: see https://docs.claude.com/en/docs/claude-code/setup
2. Aristotle command line tool for Direct: `uv tool install aristotlelib`. Then `aristotle --version`.
3. Key check. This command shows only "set" or "missing". It does not show the key:
   `if ($env:ARISTOTLE_API_KEY) { 'set' } else { 'missing' }`
   Never paste the key into a chat or a file.
4. Install the `lean4` plugin (lean4-skills by Cameron Freer) in Claude Code, as in May. Type in Claude Code:
   `/plugin marketplace add cameronfreer/lean4-skills` and then `/plugin install lean4`.
   Use the same plugin version for all four Claude Code runs. Write the version in `RUN_LOG.md`.
5. In Claude Code, type `/plugin`. Disable all other plugins (for example academic-research-skills) for the time of the runs. If the file `%USERPROFILE%\.claude\CLAUDE.md` exists, move it out of the `.claude` folder for the time of the runs. Put it back after the last run.
6. Check for MCP servers at user scope. They show in every folder. Run `cd $env:USERPROFILE` and then `claude mcp list`. If the list shows a server with "aristotle" in its name, remove it: `claude mcp remove <name> -s user`. If a plugin supplies it, disable that plugin.

## Step 2. Make the five folders (one time)

Run:

```
powershell -ExecutionPolicy Bypass -File E:\NUS\mcomp\Dissertation\publication\formalise2027\proof_round2\setup_round2.ps1
```

The script:

1. Copies the branch `lean-translate-round5-repair` from the bundle into your clone `E:\NUS\mcomp\Dissertation\CML_Proof\cakeml`.
2. Makes five worktrees under `E:\NUS\mcomp\Dissertation\r2`, each on a new branch `proof2-<run>` at `de795c9f6`.
3. For Direct, sets Lean 4.28.0 and Mathlib v4.28.0, as in commit `dd68757d7` of May, and commits this change.
4. Adds the MCP servers: lean-lsp in the four Claude Code folders, and aristotle (`septract/lean-aristotle-mcp`, as in May) in `hybrid` only. The aristotle server uses the package versions of 7 May 2026 (`uv --exclude-newer`), because it does not start with the current `mcp` 2.x package. The Aristotle server reads `ARISTOTLE_API_KEY` from your environment. The key is not written to a file.
5. Builds each project once. The first build downloads the packages and can take a long time. Warnings "declaration uses sorry" are expected. If the Direct build (Lean 4.28.0) fails, the script shows a warning. Send Claude the last 40 lines.
6. Puts a permission file `.claude\settings.local.json` in the four Claude Code folders. It allows Lean, search, and read commands without a prompt. It blocks `git push` and the `aristotle` command. Hybrid uses Aristotle only through the MCP server, as its prompt says. Git ignores this file.

At the end, read the MCP lists that the script shows. `skills`, `second-pass`, and `docs` must show lean-lsp only. `hybrid` must show lean-lsp and aristotle as connected.

## Step 3. Start a Claude Code run

Do one Claude Code run at a time. Direct can run at the same time as a Claude Code run, because Aristotle runs on the Harmonic servers.

1. Open a new PowerShell window in the project folder of the run, for example:
   `cd E:\NUS\mcomp\Dissertation\r2\skills\lean_type_sound`
   (May used the folder `lean_type_sound` as the working folder.)
2. Set the Aristotle key for this window only:
   - Skills, Second pass, Docs: `Remove-Item Env:ARISTOTLE_API_KEY -ErrorAction SilentlyContinue`. This removes the key from this window only. Thus these runs have no Aristotle, as in May.
   - Hybrid: check that the key is set: `if ($env:ARISTOTLE_API_KEY) { 'set' } else { 'missing' }`. It must show "set".
3. Start Claude Code: `claude --permission-mode acceptEdits`
4. Type `/model` and select Opus 4.7. If the list shows "Opus 4.7 (1M context)", select it. The May commit of Second pass names "Claude Opus 4.7 (1M context)". If Opus 4.7 is not in the list, stop and tell Claude.
5. Type `/effort` and select `xhigh`.
6. Type `/mcp`. Compare the servers with the table above. Only Hybrid shows an Aristotle server, and it must show "connected".
7. Write the Claude Code version, the model line, the effort, the plugins, and the MCP servers in `RUN_LOG.md`.

You can also use the Code tab of the Claude desktop app with the same folder and settings. The terminal is closer to May, and `/export` works there.

## Step 4. Send the messages

1. Open the prompt file in Notepad. Copy all of its text. Paste it into Claude Code as one message. Press Enter.
2. Do not give other instructions. Do not edit files in the folder during the run.
3. If Claude Code asks for a permission, select the option that allows the command. Write each such case in `RUN_LOG.md`.
4. When the agent stops and shows its summary, save a snapshot in a second PowerShell window. Use the run name and the number of the message that the agent finished, for example:
   `powershell -ExecutionPolicy Bypass -File E:\NUS\mcomp\Dissertation\publication\formalise2027\proof_round2\finish_run.ps1 -Run docs -Message 1`
   Then send the next message of the run, if there is one. (In May, Docs had a commit after each message. The snapshots let Claude measure each pass.)
5. Docs only: after the first summary, run `check_partial.ps1` in the second window:
   `powershell -ExecutionPolicy Bypass -File E:\NUS\mcomp\Dissertation\publication\formalise2027\proof_round2\check_partial.ps1`
   Also read the summary of the agent. If the script or the summary shows that the agent changed a def into `partial def`, send `docs_message2_only_if_partial.txt`, wait for the summary, and save a snapshot with `-Message 2`. Write this in `RUN_LOG.md`. If not, do not send message 2. Then send `docs_message3.txt`.
6. After the last summary, type `/export` and save the log in the current folder.
7. Type `/exit`.

## Step 5. Direct (Aristotle)

1. Look for the May prompt in your PowerShell history. In May you submitted it from PowerShell with `aristotle submit "..." --project-dir E:\NUS\mcomp\Dissertation\CML_Proof\cakeml\lean_type_sound --wait`. Run:
   `Select-String -Path (Get-PSReadLineOption).HistorySavePath -Pattern 'aristotle submit'`
   If it shows the May command, copy the text between the quotes into `direct\aristotle_prompt.txt` (replace all text in the file). If it shows nothing, keep the prompt that is in the file. Write in `RUN_LOG.md` which prompt you used.
2. Submit the project:
   ```
   cd E:\NUS\mcomp\Dissertation\r2\direct\lean_type_sound
   $p = (Get-Content E:\NUS\mcomp\Dissertation\publication\formalise2027\proof_round2\direct\aristotle_prompt.txt -Raw -Encoding UTF8).Trim() -replace '"', '\"'
   aristotle submit $p --project-dir . --wait
   ```
   The `-replace` part keeps double quotes in the prompt intact.
3. When the run ends, get the result: `aristotle list --limit 5` (find the project ID), then
   `aristotle download <project-id> --destination E:\NUS\mcomp\Dissertation\r2\direct_result.tar.gz`
4. Unpack the file and copy the returned project files over the files in `E:\NUS\mcomp\Dissertation\r2\direct\lean_type_sound`, as you did for commit `41c815090` in July. Keep `ARISTOTLE_SUMMARY.md`.
5. If Aristotle rejects Lean 4.28.0 or the submission fails, stop and send Claude the message.

## Step 6. Save each run

After each run, run:

```
powershell -ExecutionPolicy Bypass -File E:\NUS\mcomp\Dissertation\publication\formalise2027\proof_round2\finish_run.ps1 -Run skills
```

Use the run name: `skills`, `second-pass`, `docs`, `hybrid`, or `direct`. The script:

1. Moves the `/export` log into `claude-logs`, as in May.
2. Copies the full session transcripts (`.jsonl` files from `%USERPROFILE%\.claude\projects`) to `proof_round2\results\<run>\`.
3. Counts the Aristotle calls (MCP calls and `aristotle` commands) in all transcripts, subagents included. Skills, Second pass, and Docs must have 0. If not, the script shows a warning. Tell Claude. For Hybrid, write the count in `RUN_LOG.md`.
4. Commits all changes on the branch `proof2-<run>`.

If the script finds no transcript folder, open `%USERPROFILE%\.claude\projects`, find the folder whose name contains `r2-<run>`, and copy its `.jsonl` files to `proof_round2\results\<run>\`.

## Step 7. Give the results to Claude

After the last run, run:

```
powershell -ExecutionPolicy Bypass -File E:\NUS\mcomp\Dissertation\publication\formalise2027\proof_round2\collect_results.ps1
```

It writes `proof_round2\results\proof_round2.bundle` with all `proof2-*` branches. Then tell Claude that the results are ready. Claude reads the bundle and the transcripts from your folder and runs the same measures as in the paper (local, modulo admissions, strict audit).

## Rules

- Do not push. Claude asks for your approval before any push.
- Use the same messages for each run. Do not change the prompt text.
- Do not stop a run early. If you must stop a run, write the time and the reason in `RUN_LOG.md`.
- If a step fails, stop and send Claude the last 40 lines of the output.
