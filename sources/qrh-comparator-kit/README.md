# QRH Comparator kit

This kit lets Claude Code run an independent machine check of OpenAI's theorem that the Riemann
zeta function has no zeros with real part above 7/8, on a rented DigitalOcean machine, and then
compile your MNF bridge on top of it. You get back a receipt that says, in plain terms, what was
checked, what the checker answered, and what that answer is and is not worth.

It does not prove the Riemann Hypothesis and it cannot. It answers one question: does OpenAI's
published Lean proof of the 7/8 theorem really pass the standard judge, when someone other than
OpenAI runs it?

## What you need

- A DigitalOcean account with an SSH key added to it.
- Claude Code on your own computer, which must be a Mac, Linux, or Windows with WSL (the kit's
  commands need `bash`, `ssh` and `tar`). On plain Windows, use "The other way" below.
- The SSH key must work without typing a passphrase each time: either it has none, or it is
  loaded in your SSH agent. You will test this in step 2.
- Roughly half a day of machine time. See "Time and cost" below.

## Steps

1. **Create the droplet.** Ubuntu 24.04 (LTS) x64, type Memory-Optimized, 16 vCPUs with 128 GB
   RAM (the plan with 400 GB of disk), your SSH key as the login method. Note its IP address.
   If your account does not offer that size, DigitalOcean support has to raise your limit first.
2. **Check that you can reach it**: `ssh root@ADDRESS true` should return without asking for
   anything except, the first time, whether to trust the new machine (answer yes).
3. **Unpack the kit** on your computer and open a terminal in the `qrh-comparator-kit` folder.
4. **Start Claude Code there**: `claude`. It asks whether you trust the folder and shows the
   permissions the kit requests: a list of the kit's own `scripts/...` commands that may run
   without asking you each time. Accept. (The kit's settings also forbid edits to its own files
   and to OpenAI's code.)
5. **Give it the job.** For example:

   > The droplet's address is 203.0.113.7 and my SSH key works for root. Read CLAUDE.md and
   > carry out the protocol. I may be away for hours: keep going where CLAUDE.md lets you, and
   > stop where it says to ask me.

   Stay for the first few minutes. Its first command, `scripts/remote.sh setup ...`, is the one
   that acts as root on the droplet, and Claude Code may ask you to approve it.
6. **Wait.** There are three stretches. Setup, half an hour to an hour, mostly downloads: your
   computer has to stay awake for it. Then the real run, which takes hours and runs on the
   droplet on its own; Claude Code only looks in every nine minutes, and if your computer
   sleeps meanwhile the run does not care. Then a few minutes for the receipt and the bridge,
   for which your computer has to be awake again. If the terminal was closed or the computer
   slept, open a terminal in the same folder, run `claude --continue`, and say "carry on".
7. **Read the result.** Claude Code copies it into `results/` in this folder:
   `results/receipt/RECEIPT.md` (the verdict), `results/receipt/BRIDGE.md` (your bridge, after a
   PASS) and `results/qrh-receipt.tar.gz` (every log).
8. **Destroy the droplet** in the DigitalOcean control panel. Powering it off is not enough:
   it bills until it is destroyed.

## The other way: Claude Code on the droplet

If your computer cannot stay involved, or is plain Windows. On your computer:

```sh
scp qrh-comparator-kit.tar.gz root@ADDRESS:/root/
ssh root@ADDRESS 'tar -xzf qrh-comparator-kit.tar.gz && bash qrh-comparator-kit/scripts/00_system_setup.sh'
ssh qrh@ADDRESS
```

Then, in that session on the droplet:

```sh
curl -fsSL https://claude.ai/install.sh | bash    # Claude Code's installer; it goes to ~/.local/bin
tmux new -s qrh                                   # so a dropped connection does not end the session
cd ~/qrh-kit && ~/.local/bin/claude               # the first start walks you through logging in
```

Give it the same job, without the address. If the connection drops, log in again and run
`tmux attach -t qrh`. One caveat: your Claude login then sits in that account's home directory,
and the sandbox that runs OpenAI's code may *read* the whole disk (it cannot write outside its
own build folder and `/dev`, and cannot open TCP connections). Nothing was found in OpenAI's
files that would try, but the first way avoids the question. At the end, fetch the receipt
yourself, from your computer: `scp qrh@ADDRESS:qrh-work/qrh-receipt.tar.gz .`

## Time and cost

DigitalOcean listed the 16 vCPU / 128 GB Memory-Optimized droplet at $1.00 per hour and the
32 vCPU / 256 GB one at $2.00 per hour when this was written (2026-10-07). Check the current
price when you create it.

Expect the whole job to take between 3 and 9 hours, which is $3 to $9 at that price if the
droplet is destroyed when it is done. Nobody outside OpenAI has published a timing for this
proof. The figures below are estimates built from measurements on the small machine the kit was
tested on:

- **Setup (phases 0 to 5): 30 to 60 minutes.** Downloads, building the checker, the controls.
- **Compiling the proof: 2 to 6 hours, most likely about 2.5.** The proof is 2,924 files that
  import one another in a chain 404 levels deep, so most of them can only be compiled one after
  another. Timing 29 of the files and simulating the whole build from that gives 2.6 hours on
  16 CPUs, 3.0 on 8 and 2.4 on 32: more CPUs would not make it faster. The 29 files are the
  early, simple ones; if the later files are three times heavier per line it is 6 hours.
- **Export and kernel replay: expected to be minutes, not hours, but this is the least certain
  part.** The same two steps for a deep theorem of Mathlib (the functional equation of zeta,
  which rests on 53,000 declarations) took 3 minutes and 3.5 GB of memory there. OpenAI's
  proof adds 486,000 lines of its own on top of a similar base.
- **Receipt and bridge: 10 minutes.**

The 128 GB of memory is a deliberate margin for that least certain part, not a measured need.
The receipt records the peak memory the run really used.

## What the verdict will be

| Verdict | Meaning |
|---|---|
| PASS | Comparator accepted, in a run that started from nothing compiled: same statement, only the three standard axioms, kernel-checked. |
| REJECTED | Comparator decided against the proof. That would be news. |
| ERROR | The run ended before Comparator decided. If the machine was the cause (usually memory), it says nothing about the proof; if one of OpenAI's files did not compile, that is a finding in itself. |
| PROVISIONAL | Comparator accepted in a shortcut re-run you asked for. Encouraging, not a certification. |
| INVALID | Comparator accepted but the protocol was not followed. Not usable. |
| INCOMPLETE | No result yet: the run is still going or was not started. |

`docs/PROTOCOL.md` says exactly what a PASS certifies and what it trusts. The short version:
the theorem proved is the one stated; nothing but Lean's three standard axioms is assumed; the
kernel checked every step. It does not check that the mathematics is "morally" right beyond
that, and it does not touch the strip between 1/2 and 7/8.

If the run breaks for lack of memory, Claude Code will stop and ask you. The fix is to resize
the droplet to the next size (power off, resize "CPU and RAM only", power on) and let it start
the run again from scratch.

## After a PASS

`BRIDGE.md` lists the bridge theorems that no longer carry the 7/8 hypothesis, as Lean prints
them. Two things to know before quoting them:

- They hold inside OpenAI's Lean environment (Lean 4.34.1 and their Mathlib). Your corpus is
  pinned to Lean 4.24.0, and OpenAI's proof does not exist there. In the corpus the 7/8 theorem
  stays an explicit hypothesis; what changes is that the hypothesis now has a receipt behind it.
- The headline statement is `riemannHypothesis_iff_remaining_strip_unconditional`: RH holds if
  and only if zeta has no zeros with 1/2 < Re s <= 7/8. That is what is left. The MNF gap
  hypothesis is equivalent to RH at any threshold above 3/8, and it is still open.

## What was tested before this reached you, and what was not

Tested, on a small test machine with a working Landlock sandbox and a systemd user manager:

- every script, and the receipt's verdict logic on 95 simulated outcomes (accepts, each kind of
  rejection, crashes, interrupted launches, repeated attempts, every protocol condition broken
  in turn);
- the 21 controls (6 that must pass, 15 that must be rejected for stated reasons, including
  Comparator's own regression suite and a proof file that tries to write outside the sandbox
  while Comparator compiles it) with the exact Comparator and Lean versions the kit installs;
- fetching OpenAI's repository and verifying it against the pins; resolving all 42
  dependencies and applying OpenAI's patches, several times, with identical results;
- starting the real Comparator run on the real repository, stopping it, a warm attempt, a reset
  and a new cold attempt, with the receipt after each;
- a complete Comparator run at Mathlib's scale through the kit's launcher: Mathlib's functional
  equation of zeta as the theorem, built, exported (53,000 declarations) and replayed in the
  kernel inside the sandbox, accepted after 4 minutes;
- 29 of the proof's 2,924 files (the ones that need only the part of Mathlib built on the test
  machine): all compiled without error with the pinned Lean and Mathlib;
- both bridge files, compiled without warnings with OpenAI's Lean and Mathlib versions, and the
  whole bridge phase, twice: against a stand-in for OpenAI's theorem proved by `sorry`, where it
  must and does fail, and against a deliberately forged stand-in, where it reports success.
  (That second test is the reason the bridge phase refuses to run without a PASS: a compiled
  file can claim a theorem no kernel has checked, and only Comparator's replay catches that.)

The kit was also read by independent reviewers in three rounds, looking for ways it could
report a false PASS, ways it could fail or stall on a real droplet, and ways a genuine result
could be lost to a bookkeeping accident. What they found was fixed, and the last round found
no way to a false PASS.

Not tested, because it needs the big machine or a network path the test machine lacked:

- the full build, export and kernel replay of OpenAI's proof: the times above are estimates,
  and its memory need is not known;
- the download of Mathlib's prebuilt cache (`lake exe cache get`);
- the system setup script on a real droplet. It was run on the test machine, through the same
  `remote.sh setup` path, with a stand-in for one systemd service that machine lacks;
- the official build of the `landrun` sandbox tool. In testing, a build of the same source with
  one small library replaced by a stand-in was used, because the test machine could not
  download that library.

If something fails, it will most likely be one of those. `docs/TROUBLESHOOTING.md` covers them.

## What is in the kit

| Path | What it is |
|---|---|
| `CLAUDE.md` | The brief Claude Code works from. |
| `PINS.env` | Every commit and checksum the run is held to. |
| `KIT_MANIFEST.sha256` | Checksums of the kit's own files; the receipt checks them. |
| `scripts/` | The protocol, one script per phase, plus helpers. |
| `controls/` | Five small control projects with known right answers, and the expected outcome of Comparator's own sixteen. |
| `bridge/` | Your bridge, ported to OpenAI's Lean version, in two files. |
| `docs/PROTOCOL.md` | What is checked, what is trusted, what a PASS is worth. |
| `docs/TROUBLESHOOTING.md` | Failure by failure, what it means and who decides. |
| `NOTICE` | Sources and licences of what the kit downloads. |
