# tooling/ — Local helpers for Lean / formal-conjectures sessions

Two CLIs (`lean-doctor`, `lean-build-sweep`) plus their installers and a one-shot
CPU-saturation patch. macOS / zsh only. None of these touch the repo state ; they
live entirely under `~/.local/bin` and `~/Library/LaunchAgents`.

## What each script does

- **`lean-doctor`** — diagnostic CLI : checks free memory, swap, CPU pressure,
  zombie `lean`/`lake` processes. `--fix` proposes targeted cleanups, `--quiet`
  is for cron / launchd. Run on-demand when the Mac feels slow. Auto-runs every
  15 min once `install_lean_doctor.sh` has registered the launchd plist
  (`com.kieran.leandoctor`) ; notifies macOS only when state goes critical.
- **`lean-build-sweep`** — weekly health check across *all* active
  formal-conjectures worktrees. Runs `lake build` (incremental, fast if cached),
  records sorry count and build status, notifies only on regression. Logs to
  `~/Library/Logs/lean-build-sweep.log`. Auto-runs Sunday 03:00 once installed
  (`com.kieran.leanbuildsweep`).
- **`apply_lean_cpu_fix.sh`** — per-worktree one-shot. Caps Lean threads
  (`LEAN_NUM_THREADS=4`) in `~/.zshrc`, adds `lakebuild`/`lakecache` aliases,
  and patches `<worktree>/.vscode/settings.json` to limit the LSP. Idempotent.
  The hard-coded `PROJECT` path near the top of the script may need editing to
  match your worktree layout before first run.
- **`install_lean_doctor.sh`** / **`install_lean_build_sweep.sh`** — one-time
  global installers. Copy the CLI to `~/.local/bin/` and write a launchd plist.

## Prerequisites

- zsh (default macOS shell).
- `~/.local/bin` on `$PATH`. If missing, add to `~/.zshrc` :
  `export PATH="$HOME/.local/bin:$PATH"` then `source ~/.zshrc`.
- Optional : `brew install coreutils` for `gtimeout` (used by
  `lean-build-sweep` to cap stuck builds at 10 min).

## Install order

```sh
./tooling/install_lean_doctor.sh
./tooling/install_lean_build_sweep.sh
./tooling/apply_lean_cpu_fix.sh   # per-worktree ; edit PROJECT path first
```

## Scope

`lean-doctor` + `lean-build-sweep` are **global** (one user, all worktrees) once
installed. `apply_lean_cpu_fix.sh` patches a single worktree's
`.vscode/settings.json` ; the `~/.zshrc` half is global and idempotent.
