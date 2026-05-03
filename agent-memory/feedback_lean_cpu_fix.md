# Lean / Mathlib — Fix CPU 100 %

## Symptôme récurrent
Mac (M4, 16 Go RAM) sature à 100 % CPU pendant les sessions Lean : un `git checkout` entre branches du projet `formal-conjectures` (mainline ↔ track-c-1dkmt ↔ track-d-btis-honest) invalide le `.lake/build/`, ce qui force `lake build` à re-élaborer Mathlib + le projet (~30-60 min CPU saturé, RAM tape dans le swap, Mac inutilisable). Cas TC5/`bzlql9x9b` documenté.

## Fix principal — git worktrees, un par branche
Le fichier de référence est `~/Documents/formal-conjectures/worktree-setup-guide.md`.

État actuel :
```
~/Documents/formal-conjectures           [r46-track-a-mge-posdef]   ← mainline
~/Documents/formal-conjectures-track-c   [track-c-1dkmt]            ← Track C / Erdős 524
~/Documents/formal-conjectures-track-d   [track-d-btis-honest]      ← Track D
```

Chaque worktree partage le même `.git` mais possède son propre `.lake/build/` et son propre serveur LSP tiède. **Plus jamais de `git checkout`** : on `cd` au worktree de la branche.

### Création d'un worktree
```bash
cd ~/Documents/formal-conjectures
git worktree add ../formal-conjectures-<nom> <branch>
cd ../formal-conjectures-<nom>
lake exe cache get          # MANDATORY — ~2-5 min vs 30-60 min de cold compile
```

### ⚠️ Règle liante (BINDING RULE)
`lake exe cache get` est **obligatoire** :
- après chaque `git worktree add` (premier setup),
- après chaque `lake update mathlib` (pin bump),
- après tout bump de toolchain qui invalide `.lake/build/`,
- au premier clone du projet sur une nouvelle machine.

Coût d'un skip : ~30-60 min CPU à 100 %, RAM saturée, Mac figé.

### Pin-bump (Mathlib) — protocole
Bump dans **un seul worktree** (dédié), jamais en mainline :
```bash
cd ~/Documents/formal-conjectures-track-d
# editer lakefile.toml → bump mathlib rev
lake update mathlib
lake build              # vérifie le nouveau pin
```
Les autres worktrees restent sur l'ancien pin via leur `lake-manifest.json` figé. C'est ce qui a tué TD4 quand le pin a été bump en mainline pendant que les autres tracks tournaient.

## Anti-patterns (du worktree-setup-guide)
- ❌ Deux sessions parallèles sur le même worktree.
- ❌ `git checkout` cross-worktree (échoue : "branch already checked out").
- ❌ Symlink/partage du `.lake/build/` entre worktrees.
- ❌ Pin-bump en mainline sans coordination FS-window.

## Mesures secondaires (en complément, pas en remplacement)
Si après mise en place des worktrees le CPU reste haut pendant un build actif :

### `~/.zshrc`
```sh
export LEAN_NUM_THREADS=4
alias lakebuild='lake build -j 4'
alias lakecache='lake exe cache get'
alias lakebuild-bg='taskpolicy -b lake build -j 4'   # E-cores : compile lent, Mac fluide
```

### `.vscode/settings.json` du worktree actif
```json
"lean4.serverEnv": { "LEAN_NUM_THREADS": "4" },
"lean4.autoOpenInfoView": false
```

### Hygiène runtime
- Fermer onglets Lean inactifs dans VS Code (1 buffer = 1 worker LSP).
- `killall ollama` si modèle local pas en usage.
- Quitter RustDesk si pas de session distante.
- Limiter le nombre de Cowork actifs (chacun = un Service de machine virtuelle pour Claude).

## Lien avec autres feedbacks
Voir `feedback_v2_cluster_filesystem_discipline.md` : les pin-bumps + `lake update` + checkouts `.lake/packages/` mutent l'état partagé. Les worktrees résolvent cette discipline FS en isolant chaque branche dans son propre dossier.
