---
name: reflect
description: Spawn three parallel review subagents over the active transcript, surface learnings, and route each to a concrete edit on an existing skill. Use when the user says reflect.
disable-model-invocation: true
---

# Reflect

Mine the current conversation for durable learnings, then route them into skill edits.

Invoke when the user says "reflect" or "/reflect". Skip when the conversation is trivial, off-topic, or already covered by an existing skill the parent followed correctly. One-offs are not learnings.

## 1. Locate the active transcript

Before fanning out, find this conversation's transcript in the active workspace's session directory. Do not glob across every project's directory. That crosses workspace boundaries and reads private chats from unrelated projects.

Where the transcript lives depends on your harness:

- **Cursor:** the `agent-transcripts/` directory the system prompt names.

  ```bash
  ls -t <agent-transcripts>/*.jsonl <agent-transcripts>/*/*.jsonl <agent-transcripts>/*/subagents/*.jsonl 2>/dev/null | head -10
  ```

  That covers the legacy flat (`<id>.jsonl`), current nested (`<id>/<id>.jsonl`), and subagent (`<parent>/subagents/<child>.jsonl`) layouts. For each candidate, read the first JSONL line. Take the file whose `message.content[0].text` contains the conversation's opening user prompt.
- **Claude Code:** `~/.claude/projects/<slug>/<session-id>.jsonl`, where `<slug>` is the workspace path with every character that isn't a letter or digit turned into "-". When the work ran in sessions this one started, each of those has its own transcript in the slug folder of its own worktree, with its subagents under `<session-id>/subagents/`. Gather them too. The desktop app's `local_` session IDs don't match transcript file names, so match each by its `gitBranch` field or its title.
- **Pi:** `~/.pi/agent/sessions/--<slug>--/*.jsonl`, where `<slug>` is the workspace path with the leading slash dropped and each "/" turned into "-".
- **Codex:** `~/.codex/sessions/YYYY/MM/DD/rollout-*.jsonl`. Keep only files whose first line has `payload.cwd` equal to the workspace path.
- **Other harnesses:** check the harness's session directory for this workspace.

Outside Cursor, take the newest candidates first and confirm one by finding the conversation's opening user prompt in its first user message. If none matches, pass a tight digest of the session instead.

## 2. Spawn three reviewers in parallel

One message, three `Task` calls, `subagent_type: generalPurpose`, agent mode (`readonly: false`). Reviewers need MCP access to look up the tickets, chat threads, and observability traces the transcript references, and readonly strips MCPs.

**Other harnesses.** The spawns in this skill use Cursor's `Task` tool. In another harness, use its subagent tool: `Agent` in Claude Code (`subagent_type: general-purpose`), `task` in OpenCode (`subagent_type: general`), `spawn_agent` in Codex. Keep the prompt and the model. Drop parameters your tool doesn't have. If your harness has no subagent tool, as in Pi without an extension, run each role yourself, one after another.

Each reviewer and the synthesizer name a role line in the pstack settings file (`~/.cursor/rules/pstack-models.mdc` in Cursor, `~/.agents/pstack-models.md` in other harnesses) and a default. Set `model` to that line's value, or to the default if the file or the line is missing. Leave `model` unset when the value is `auto` or `inherit-parent`. If your subagent tool rejects a slug, use the default and say so. If it rejects the default, use the closest valid slug of the same family from its error message or your harness's model list. Pick each subagent's reasoning level and fast or standard speed for the job, per the Subagents section of the **poteto-mode** skill.

| Lens | Role line | Default `model` | Prompt template |
|---|---|---|---|
| Judgment | `reflect judgment, divergent, synthesizer` | `claude-opus-5-5-xhigh` | `references/judgment-reviewer.md` |
| Tooling | `reflect tooling` | `grok-4.7-xhigh-fast` | `references/tooling-reviewer.md` |
| Divergent | `reflect judgment, divergent, synthesizer` | `claude-opus-5-5-xhigh` | `references/divergent-reviewer.md` |

Pass each template verbatim, substituting the transcript path or digest where marked. Append one line naming that reviewer's own scratch folder, such as `<scratchpad>/reflect-judgment/`, since parallel reviewers sharing a folder overwrite each other's files. Reviewers return findings in the `Task` response body.

## 3. Synthesize

One `Task` call, `subagent_type: generalPurpose`, `model` from the `reflect judgment, divergent, synthesizer` line (default `claude-opus-5-5-xhigh`), agent mode (`readonly: false`). It spot-verifies citations through MCP, and readonly strips MCPs. Pass `references/synthesizer.md` verbatim, with each reviewer's full output inlined where marked. It returns an Accepted / Rejected / Backlog list.

## 4. Structural enforcement check

Move any Accepted item that a lint rule, script, metadata flag, or runtime check would enforce more reliably to Backlog. See the **encode-lessons-in-structure** principle skill.

## 5. Apply

Present the synthesizer's full Accepted / Rejected / Backlog output and wait for explicit approval before applying any Accepted edit. The user picks the subset and may redirect routings. Skill changes affect every future agent in the org. Do not auto-apply.

File each Backlog item to your team's devex or backlog tracker without waiting. Only the Accepted list waits for approval. If the project's instructions require approval before filing, present the Backlog with the Accepted list and file only the items the user picks.

Before the first edit, confirm which checkout and branch the skill files are in. Skill edits go on their own branch, never on a branch that belongs to another task.

Follow each approved row's Routing exactly:

- Trivial existing-skill edit (a one-line bullet, a tightened sentence, a stale fact corrected): the parent does it directly.
- Substantive existing-skill edit (a new section, a new pattern table, more than ~10 lines): hand to your harness's skill-authoring skill and run its draft / test / iterate loop. That is `create-skill` in Cursor (built in) or Anthropic's `skill-creator`. If you have neither, follow the Agent Skills format at agentskills.io. "`create-skill`" below means whichever of these you use.
- `tune description: <skill path>` (the skill exists but didn't trigger when it should have): hand to `create-skill` and run its description-optimization loop.
- `new skill via create-skill: <kebab-name>`: hand creation to `create-skill`. Do not invent the shape ad hoc.

If your environment ships a SKILL.md validator, run it on every touched skill before declaring done.

After applying edits, tell each running session that loaded a changed skill to invoke it again by name. A session keeps the skill text it loaded first, also across compaction, so it skips exactly the steps an edit adds.

## 6. Summarize for the user

Short list, no preamble:

- Edits applied: `<skill path>`. What changed, one line each.
- New skills created: `<skill path>`. One line each (rare).
- Backlog filed to the devex tracker: `<issue title>` (`<tags>`). One line each.
- Dropped: one line per rejected finding + reason from the synthesizer.
