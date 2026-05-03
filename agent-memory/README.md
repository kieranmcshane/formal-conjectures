# agent-memory/ — Discipline notes from Claude Cowork sessions

These are per-user "feedback memory" files that Claude Cowork loads
automatically on session start. They encode discipline rules learned during the
project — bridge-gap audits before claiming axiom retirement, never claim a
build success without `lake build` running clean, worktree filesystem hygiene,
etc.

## Files

- `MEMORY.md` — the index Cowork uses to find each entry.
- `feedback_*.md` — one rule per file (rule, why, how to apply).

## Install for Claude Cowork

If your local user is `<your-username>`, copy these into your Cowork memory dir :

```sh
cp agent-memory/* ~/.claude/projects/-Users-<your-username>/memory/
```

The directory name encodes the absolute project path, so if your checkout lives
somewhere other than `~/Documents/formal-conjectures` the directory name will
differ — check `~/.claude/projects/` for the right one.

## Other AI clients (Codex, Gemini, etc.)

These notes are not auto-loaded. Paste the relevant `feedback_*.md` content
into your prompt when the topic applies. `MEMORY.md` is a one-line index of
which file covers which rule.
