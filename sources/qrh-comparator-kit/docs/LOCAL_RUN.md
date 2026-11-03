# Running the kit on your own Ubuntu machine

Same protocol as the droplet, on a laptop you own. Target: ThinkPad T14 G1, 40 GB RAM,
Ubuntu 26.04. Needs at least 30 GB RAM and 100 GB free disk; the kernel must have Landlock
(any Ubuntu from 22.04 on does).

## One-time setup (as yourself, with sudo)

```sh
cd ~
tar -xzf qrh-comparator-kit.tar.gz
QRH_LOCAL=1 QRH_SWAP_GB=32 sudo -E bash qrh-comparator-kit/scripts/00_system_setup.sh
```

This installs the packages, creates the unprivileged user `qrh` that everything else runs as,
adds a 32 GB swap file as a cushion, and installs the kit read-only at /opt/qrh-kit. It ends
with `[setup] done`.

Keep the machine awake: Settings > Power > Screen Blank: Never, Automatic Suspend: Off,
Power Mode: Performance. Plug it in.

## Start Claude Code as the `qrh` user

```sh
sudo machinectl shell qrh@
```

That opens a shell as `qrh` with its own systemd session (needed for the sandbox restrictions;
`su` would not do). In it:

```sh
curl -fsSL https://claude.ai/install.sh | bash
tmux new -s qrh
cd ~/qrh-kit && ~/.local/bin/claude
```

The first start asks you to log in: it prints a link; open it in the browser on this same
machine and finish there. Accept the folder-trust prompt. Then give it the job:

> Read CLAUDE.md and carry out the protocol. This is my own laptop, not a droplet. I may be
> away for hours: keep going where CLAUDE.md lets you, and stop where it says to ask me.

Leave the terminal open, or detach with Ctrl-b then d and come back with
`sudo machinectl shell qrh@` then `tmux attach -t qrh`. Expect most of a day.

## Afterwards

The receipt is at `/home/qrh/qrh-work/qrh-receipt.tar.gz`. Copy it to your own account:

```sh
sudo cp /home/qrh/qrh-work/qrh-receipt.tar.gz ~/ && sudo chown $USER ~/qrh-receipt.tar.gz
```
