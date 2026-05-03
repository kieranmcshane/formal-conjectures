#!/bin/zsh
# apply_lean_cpu_fix.sh
# ----------------------------------------------------------------------
# Réduit la charge CPU que Lean / lake / Lean LSP mettent sur ton Mac.
# Combo : (1) limite le parallélisme de lake, (4) cap des threads du
# serveur Lean dans VS Code, (7) raccourci pour récupérer le cache
# précompilé Mathlib avant tout build.
#
# Idempotent : ré-exécutable sans casse, fait un backup avant chaque
# modification.
# ----------------------------------------------------------------------

set -e

ZSHRC="$HOME/.zshrc"
PROJECT="$HOME/Documents/formal-conjectures-track-c"
VSCODE_SETTINGS="$PROJECT/.vscode/settings.json"

THREADS=4   # M4 a 4 P-cores ; on les utilise tous pour Lean, laisse les E-cores au système

echo "==> 1/3  Backup"
cp "$ZSHRC" "$ZSHRC.bak.$(date +%Y%m%d-%H%M%S)"
[ -f "$VSCODE_SETTINGS" ] && cp "$VSCODE_SETTINGS" "$VSCODE_SETTINGS.bak.$(date +%Y%m%d-%H%M%S)"

# ----------------------------------------------------------------------
echo "==> 2/3  ~/.zshrc : LEAN_NUM_THREADS + alias"
if ! grep -q "LEAN_NUM_THREADS" "$ZSHRC"; then
  cat >> "$ZSHRC" <<EOF

# ── Lean / Mathlib : cap CPU (ajouté par apply_lean_cpu_fix.sh) ──
export LEAN_NUM_THREADS=$THREADS
alias lakebuild='lake build -j $THREADS'
alias lakecache='lake exe cache get'
alias lakebuild-bg='taskpolicy -b lake build -j $THREADS'   # force E-cores : compile lent, Mac réactif
EOF
  echo "    ajouté."
else
  echo "    déjà présent — skip."
fi

# ----------------------------------------------------------------------
echo "==> 3/3  $VSCODE_SETTINGS : lean4.serverEnv"
if [ ! -f "$VSCODE_SETTINGS" ]; then
  echo "    settings.json absent — skip (projet introuvable ?)"
else
  # Utilise python pour éditer le JSON proprement (préserve les commentaires JSON5
  # via une regex simple sur la dernière "}" — settings.json VS Code accepte les commentaires
  # mais les parsers JSON stricts non). Plus sûr : python avec un parser tolérant.
  python3 <<PY
import re, pathlib
p = pathlib.Path("$VSCODE_SETTINGS")
src = p.read_text()
if "lean4.serverEnv" in src:
    print("    déjà présent — skip.")
else:
    # Insertion juste avant la dernière accolade fermante de l'objet racine
    insertion = '''
  ,
  // ── Lean LSP : cap CPU (ajouté par apply_lean_cpu_fix.sh) ──
  "lean4.serverEnv": {
    "LEAN_NUM_THREADS": "$THREADS"
  },
  "lean4.autoOpenInfoView": false
'''
    # Trouve la dernière "}" non-imbriquée
    new = re.sub(r'\}\s*\Z', insertion + '\n}\n', src, count=1)
    # Nettoie une éventuelle virgule en trop si la dernière clé existante en avait déjà une
    new = re.sub(r',\s*,\s*//', ',\n  //', new)
    p.write_text(new)
    print("    ajouté.")
PY
fi

echo
echo "─────────────────────────────────────────────"
echo "Fait. Pour activer immédiatement :"
echo "  source ~/.zshrc"
echo "  # puis dans VS Code : Cmd+Shift+P → 'Developer: Reload Window'"
echo
echo "Workflow Lean recommandé :"
echo "  lakecache              # 1. récupère les .olean précompilés (gratuit, depuis Azure)"
echo "  lakebuild              # 2. build avec -j $THREADS au lieu de tous les cœurs"
echo "  lakebuild-bg           # variante : compile sur E-cores, Mac reste fluide"
echo "─────────────────────────────────────────────"
