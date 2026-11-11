= Reproducing and verifying the record <sec-reproducing-and-verifying-the-record>

== Verifying the record offline <sec-verifying-the-record-offline>

In a copy of the record:

```
sha256sum -c CHECKSUMS.sha256
./verify_deposit.sh
```

The first command checks the sha256 of the 27 listed files: the 21 tarballs and six other top-level files.
`README.md`, `sources/` and `notes/` are not listed.

The second needs `sha256sum`, `tar` and `python3` and runs neither Lean nor Comparator.
It repeats the first check; checks in the bundles the verdict PASS, the run type cold and the pinned commit of runs 1 and 2, and the result line ACCEPTED of runs 3 to 11; checks that the Lean sources hashed by the receipts of runs 3 to 5 and 7 to 11 are byte-identical to those in the matching add-on tarball (not for run 6), and each add-on against its own manifest; and, with network access, compares the two upstream statement files at the pinned commits with the pins.
Run at the commit cited in~@sec-availability, it ended in `VERIFY=OK`; the counts given here (27 listed files, 21 tarballs) are those of that commit.

The first establishes that the files are those the record cites; the second, that the bundles carry the verdicts reported here (for runs 2 and 7 to 11 also the theorem counts) and that the Lean sources hashed by the receipts of runs 3 to 5 and 7 to 11 are the published ones.
Neither shows that a run took place as recorded; for that, in the protocol's words, "Anyone with the same kit can repeat the run."

== Repeating a run <sec-repeating-a-run>

The kit needs a Linux machine with Landlock and a systemd user session; its notes for a local run ask for at least 30 GB of memory and 100 GB of free disk.
A setup script run as root creates the unprivileged account `qrh` and installs the kit read-only; every later phase runs as that account.
On the laptop used here (8 CPUs, 37 GB of memory) the Comparator job took 1 h 54 min 37 s in run 1, 21 minutes in run 2 and at most 16 minutes in each of runs 3 to 11.

Each add-on is a tarball with a manifest, a README and an instruction file for Claude Code; the commands can also be typed by hand.
A run on a verified tree takes three scripts.
The first checks the add-on against its manifest, requires the PASS of the run whose tree it uses, puts the Lean files and the challenge in place and starts Comparator in a detached unit; the second reports the state of the job; the third writes the report and the bundle and ends in `ACCEPTED`, `REJECTED` or `INCOMPLETE`.
The instructions state: "A REJECTED result is a real result."

A repeat depends on the servers that hold the pinned commits and Mathlib's prebuilt cache; the standalone Comparator repository is archived~@comparator, and its two pinned tags still resolved when this paper was prepared.

== Availability <sec-availability>

The record is the public repository https://github.com/Joeyxyxyz/qrh-comparator-receipts; everything said here refers to commit `9a6a1d9760847fb63e071c73b5f6c9c85f766653`, which corrects documents of the record as listed in~@sec-errata; this paper, its source and its review record were added to the repository in the commit after it.
It holds the 21 tarballs (the kit, nine add-ons, eleven receipt bundles), the checksum file, the verifier, the register, unpacked copies of the kit and the add-ons under `sources/`, and the working notes of runs 7 to 11 under `notes/`.
The 23 Lean files of the complete layer are in `sources/qrh-zeta23-addon-v6/`.
This paper is deposited on Zenodo.
The register and `NOTICE` speak of a "Zenodo record of 2026-10-29", a deposit of runs 1 to 6 prepared at that date; no file of the record gives a DOI for it, and this paper does not rely on it.
The repository's `zenodo-metadata.json` describes the deposit of this paper with a snapshot of the record.
The two artifacts under test are not redistributed; the scripts fetch them at the pinned commits~@openai-math #cite(<anthropic-formal-math>).

== Licenses <sec-licenses>

The files authored for the record (the kit and add-on scripts and documents, the author's Lean files, the receipts) are under the Apache License 2.0, as `LICENSE` states.
`NOTICE` names the third-party tools that the scripts download, which keep their own licenses, and the two quotations in the receipts: OpenAI's nine-line challenge file and Anthropic's `Challenge.lean`, both Apache-2.0.
The text of this paper is under CC BY 4.0.
