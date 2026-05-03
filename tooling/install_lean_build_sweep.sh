#!/bin/zsh
# Installe lean-build-sweep + le plist launchd hebdomadaire (dimanche 03:00).
set -e

OUT="$(cd "$(dirname "$0")" && pwd)"
DEST="$HOME/.local/bin/lean-build-sweep"

mkdir -p "$HOME/.local/bin" "$HOME/Library/Logs" \
  "$HOME/Library/Caches/lean-build-sweep" "$HOME/Library/LaunchAgents"

cp "$OUT/lean-build-sweep" "$DEST"
chmod +x "$DEST"
echo "✓ installé : $DEST"

PLIST="$HOME/Library/LaunchAgents/com.kieran.leanbuildsweep.plist"
cat > "$PLIST" <<EOF
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
  <key>Label</key>
  <string>com.kieran.leanbuildsweep</string>
  <key>ProgramArguments</key>
  <array>
    <string>/bin/zsh</string>
    <string>-l</string>
    <string>-c</string>
    <string>$DEST --quiet >> $HOME/Library/Logs/lean-build-sweep.log 2>&amp;1</string>
  </array>
  <key>StartCalendarInterval</key>
  <dict>
    <key>Weekday</key>
    <integer>0</integer>
    <key>Hour</key>
    <integer>3</integer>
    <key>Minute</key>
    <integer>0</integer>
  </dict>
  <key>RunAtLoad</key>
  <false/>
  <key>StandardOutPath</key>
  <string>$HOME/Library/Logs/lean-build-sweep.log</string>
  <key>StandardErrorPath</key>
  <string>$HOME/Library/Logs/lean-build-sweep.err</string>
</dict>
</plist>
EOF

launchctl unload "$PLIST" 2>/dev/null || true
launchctl load "$PLIST"

echo "✓ launchd actif : sweep tous les dimanches 03:00"
echo "  log     : ~/Library/Logs/lean-build-sweep.log"
echo "  state   : ~/Library/Caches/lean-build-sweep/last-state.tsv"
echo
echo "Pour tester immédiatement (sans attendre dimanche) :"
echo "  lean-build-sweep --dry        # liste les worktrees, zéro build"
echo "  lean-build-sweep              # vrai sweep, sortie verbeuse"
echo
echo "Pour suspendre / réactiver / désinstaller :"
echo "  launchctl unload ~/Library/LaunchAgents/com.kieran.leanbuildsweep.plist"
echo "  launchctl load   ~/Library/LaunchAgents/com.kieran.leanbuildsweep.plist"
echo "  rm ~/Library/LaunchAgents/com.kieran.leanbuildsweep.plist"
