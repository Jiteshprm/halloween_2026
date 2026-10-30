mkdir -p ~/.config/systemd/user
cat > ~/.config/systemd/user/monster.service << 'EOF'
[Unit]
Description=Halloween voice-changer monster
After=pipewire.service pipewire-pulse.service wireplumber.service
Wants=pipewire.service pipewire-pulse.service wireplumber.service

[Service]
WorkingDirectory=%h/halloween_2026
ExecStart=%h/halloween_2026/venv/bin/python -u %h/halloween_2026/monster.py
Restart=always
RestartSec=5

[Install]
WantedBy=default.target
EOF
systemctl --user daemon-reload
systemctl --user enable --now monster.service
sudo loginctl enable-linger birdofprey
