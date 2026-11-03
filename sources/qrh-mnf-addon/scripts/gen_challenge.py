import re, json, sys
from pathlib import Path
files = ["MNF/RH/Core.lean", "MNF/RH/Gap.lean", "MNF/RH/Hypotheses.lean", "MNF/RH/Unconditional.lean"]
want_thms = Path("MNFChallenges/theorem_list.txt").read_text().split()
defs, thms = [], []
for f in files:
    lines = Path(f).read_text().split("\n")
    i = 0
    while i < len(lines):
        l = lines[i]
        m = re.match(r"^(noncomputable def|def|theorem) (\S+)", l)
        if m:
            kind, name = m.group(1), m.group(2)
            block = [l]; j = i
            while not (lines[j].rstrip().endswith(":= by") or lines[j].rstrip().endswith(":=")):
                if kind != "theorem" and ":=" in lines[j]: break
                j += 1; block.append(lines[j])
            if kind == "theorem":
                if name in want_thms:
                    text = "\n".join(block)
                    text = re.sub(r":= by\s*$", ":= by\n  sorry", text)
                    if not text.endswith("sorry"): text = re.sub(r":=\s*$", ":=\n  sorry", text)
                    thms.append((name, text))
            else:
                k = i
                while k + 1 < len(lines) and lines[k+1].strip() != "": k += 1
                defs.append((name, "\n".join(lines[i:k+1])))
            i = j + 1
        else: i += 1
missing = [n for n in want_thms if n not in [t[0] for t in thms]]
assert not missing, missing
out = ["/-", "MNF × RIEMANN ZETA — COMPARATOR CHALLENGE  (MNFChallenges/RH.lean)",
"The statements of the MNF.RH library with every proof replaced by `sorry`, and the",
"definitions they refer to, copied verbatim from MNF/RH/*.lean by gen_challenge.py.",
"Comparator builds this file and the solution (MNF.RH.Unconditional), exports both, and",
"checks that every definition and every theorem statement agrees, and that the solution's",
"proofs use no axiom beyond propext, Quot.sound, Classical.choice.", "-/",
"import Mathlib", "", "namespace MNF.RH", "", "open Complex Filter Topology", "open scoped Real", ""]
for n, d in defs: out += [d, ""]
for n, t in thms: out += [t, ""]
out.append("end MNF.RH")
Path("MNFChallenges/RH.lean").write_text("\n".join(out) + "\n")
cfg = {"challenge_module": "MNFChallenges.RH", "solution_module": "MNF.RH.Unconditional",
       "theorem_names": ["MNF.RH." + n for n, _ in thms], "definition_names": ["MNF.RH." + n for n, _ in defs],
       "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"], "enable_nanoda": False}
Path("MNFChallenges/RH.json").write_text(json.dumps(cfg, indent=2) + "\n")
print(len(defs), "definitions,", len(thms), "theorems")
