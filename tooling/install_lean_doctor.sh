#!/bin/zsh
# Installe lean-doctor dans ~/.local/bin (déjà dans ton PATH via ~/.zshrc).
set -e

OUT="$(cd "$(dirname "$0")" && pwd)"
DEST="$HOME/.local/bin/lean-doctor"

mkdir -p "$HOME/.local/bin"
cp "$OUT/lean-doctor" "$DEST"
chmod +x "$DEST"
echo "✓ installé : $DEST"

# Test rapide
if command -v lean-doctor >/dev/null 2>&1; then
  echo "✓ lean-doctor accessible dans le PATH"
else
  echo "⚠ pas dans le PATH — vérifie que ~/.zshrc contient bien :"
  echo "    export PATH=\"\$HOME/.local/bin:\$PATH\""
  echo "    (puis : source ~/.zshrc)"
fi

echo
echo "Usage :"
echo "  lean-doctor             # diagnostic"
echo "  lean-doctor --fix       # diagnostic + propose nettoyages"
echo "  lean-doctor --fix -y    # nettoyages sans confirmation"
echo "  lean-doctor --quiet     # silencieux + notif macOS si problème"
echo

# ─── Installation du launchd périodique ──────────────────────────
PLIST="$HOME/Library/LaunchAgents/com.kieran.leandoctor.plist"
mkdir -p "$HOME/Library/LaunchAgents" "$HOME/Library/Logs" "$HOME/Library/Caches/lean-doctor"

cat > "$PLIST" <<EOF
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
  <key>Label</key>
  <string>com.kieran.leandoctor</string>
  <key>ProgramArguments</key>
  <array>
    <string>/bin/zsh</string>
    <string>-c</string>
    <string>$DEST --quiet >> $HOME/Library/Logs/lean-doctor.log 2>&amp;1</string>
  </array>
  <key>StartInterval</key>
  <integer>900</integer>
  <key>RunAtLoad</key>
  <true/>
  <key>StandardOutPath</key>
  <string>$HOME/Library/Logs/lean-doctor.log</string>
  <key>StandardErrorPath</key>
  <string>$HOME/Library/Logs/lean-doctor.err</string>
</dict>
</plist>
EOF

# Recharger proprement (si déjà chargé, on décharge d'abord)
launchctl unload "$PLIST" 2>/dev/null || true
launchctl load "$PLIST"

echo "✓ launchd actif : check toutes les 15 min"
echo "  log    : ~/Library/Logs/lean-doctor.log"
echo "  histo  : ~/Library/Caches/lean-doctor/history.log"
echo
echo "Pour suspendre temporairement :"
echo "  launchctl unload ~/Library/LaunchAgents/com.kieran.leandoctor.plist"
echo "Pour réactiver :"
echo "  launchctl load   ~/Library/LaunchAgents/com.kieran.leandoctor.plist"
echo "Pour désinstaller complètement :"
echo "  launchctl unload ~/Library/LaunchAgents/com.kieran.leandoctor.plist"
echo "  rm ~/Library/LaunchAgents/com.kieran.leandoctor.plist"
