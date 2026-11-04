#!/usr/bin/env python3
"""Generate the Comparator challenge of the density layer (QRH zeta23 add-on v2, step B3, v6).

Run from the project directory (zeta23/) after the layer's files are in place:
    python3 -I <addon>/scripts/z23_gen_density_challenge.py

A mirror is the source module itself with (a) every non-Mathlib import replaced by the import of
the corresponding mirror module or dropped, and (b) every theorem's proof replaced by `sorry`.
Definitions, instances, namespaces, sections, opens, set_options and comments are kept verbatim
and in order, so each mirror is module-for-module the same as its source: Lean abstracts the
proof terms inside definitions into auxiliary lemmas numbered per module, and Comparator compares
definition bodies (`definition_names` is empty), so a mirror that was not laid out exactly like
its source would make some definition's auxiliary lemma differ and be rejected. The challenge is
MNFChallengesD.All (which imports every mirror); the solution is MNF.RH.DensityAll.
"""
import json
import re
from pathlib import Path

# source module -> mirror module, in dependency order
MIRROR = {
    "MNF.RH.Core": "MNFChallengesD.Core",
    "MNF.RH.Gap": "MNFChallengesD.Gap",
    "MNF.RH.Hypotheses": "MNFChallengesD.Hypotheses",
    "MNF.RH.Counting": "MNFChallengesD.Counting",
    "MNF.RH.GapDensity": "MNFChallengesD.GapDensity",
    "Zeta23.BohrLandau": "MNFChallengesD.BohrLandau",
    "MNF.RH.Density": "MNFChallengesD.Density",
    "MNF.Extension.InjectionEjection": "MNFChallengesD.Extension",
    "MNF.RH.Strip": "MNFChallengesD.Strip",
    "Zeta23.BL.DPMV": "MNFChallengesD.DPMV",
    "Zeta23.BL.DPMVexp": "MNFChallengesD.DPMVexp",
    "Zeta23.BL.JensenDisc": "MNFChallengesD.JensenDisc",
    "Zeta23.BL.BohrLandauPartial": "MNFChallengesD.BohrLandauPartial",
    "MNF.RH.DensityPartial": "MNFChallengesD.DensityPartial",
    "Zeta23.BL.BohrLandauClosure": "MNFChallengesD.BohrLandauClosure",
    "MNF.RH.ReservoirMass": "MNFChallengesD.ReservoirMass",
    "Zeta23.Density.StripDensity": "MNFChallengesD.StripDensity",
}
# modules whose theorems the configuration lists (the claim set)
CLAIMED = ["MNF.RH.GapDensity", "MNF.RH.Density", "MNF.RH.Strip", "MNF.Extension.InjectionEjection",
           "Zeta23.BL.DPMV", "Zeta23.BL.DPMVexp", "Zeta23.BL.JensenDisc",
           "Zeta23.BL.BohrLandauPartial", "MNF.RH.DensityPartial", "Zeta23.BL.BohrLandauClosure", "MNF.RH.ReservoirMass",
           "Zeta23.Density.StripDensity"]
CHALLENGE_MODULE, SOLUTION_MODULE = "MNFChallengesD.All", "MNF.RH.DensityAll"
# declarations omitted from a mirror (and from the claim set) because their statements mention
# zeta23-internal objects (Zeta23.Ncount, ell1, zetaZeroConfig, Zeta23.reflect) or a constant
# fixed by Classical.choose (CG, meanSquareB, A₀), or use a finiteness proof as a term (`.toFinset`, which
# makes Comparator compare that proof); the results claimed in their place are the
# existential / MNF-vocabulary statements that follow them in the same file
EXCLUDE = {
    "MNF.RH.ReservoirMass": {"CG_nonneg", "CG_spec", "zeta_approx_segment_half", "meanSquare_sharp_param_half",
        "meanSquareB_nonneg", "meanSquare_explicit_small_B", "meanSquareUnifFrom_explicit", "meanSquareUnifFrom_explicit'",
        "NRight_explicit", "A₀_nonneg", "Ncount_self", "Ncount_zero_nat", "Ncount_unit_le", "Ncount_le_mul_log",
        "ell1_half", "mul_log_le_Ncount", "MNF_Ncount_eq", "reflect_re", "reflect_im", "reflect_reflect",
        "reflect_injective", "reflect_mem_zerosIn", "zeta_order_reflectZ", "reflect_bijOn", "reflect_bijOn_zerosIn",
        "NOff_eq_sum_ite", "NOff_real_eq_sum_indicator"},
}
DECL_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?P<mod>(?:private |protected )*)(?P<kind>theorem|lemma)\s+(?P<name>\S+)")

def path_of(mod):
    return Path(*mod.split(".")).with_suffix(".lean")

def mirror(src_mod, out_mod):
    lines = path_of(src_mod).read_text().split("\n")
    out, claimed, ns = [], [], []
    excl = EXCLUDE.get(src_mod, set())
    doc = []   # a pending doc comment, emitted with its declaration or dropped with it
    i = 0
    while i < len(lines):
        l = lines[i]
        if l.startswith("/--"):
            k = i
            while "-/" not in lines[k]:
                k += 1
            doc = lines[i:k + 1]
            i = k + 1
            continue
        if l.startswith("import "):
            mod = l[len("import "):].strip()
            if mod.startswith("Mathlib"):
                out.append(l)
            elif mod in MIRROR:
                out.append("import " + MIRROR[mod])
            # any other non-Mathlib import (zeta23's own modules) is dropped: the mirror is Mathlib-only
            i += 1
            continue
        m = re.match(r"^namespace\s+(\S+)", l)
        if m:
            ns.append(("ns", m.group(1)))
        elif re.match(r"^(noncomputable\s+)?section\b", l):
            ns.append(("sec", l.split()[-1] if not l.rstrip().endswith("section") else ""))
        elif re.match(r"^end\b", l):
            if ns:
                ns.pop()
        d = DECL_RE.match(l)
        if d:
            k = i
            while k + 1 < len(lines) and (lines[k + 1].startswith((" ", "\t")) and lines[k + 1].strip() != ""):
                k += 1
            if d.group("name") in excl:
                doc = []
                i = k + 1
                continue
            block = "\n".join(lines[i:k + 1])
            j = block.index(":=")
            out.extend(doc); doc = []
            out.append(block[:j] + ":= by\n  sorry")
            if "private" not in d.group("mod") and not d.group("name").startswith("aux_"):
                prefix = ".".join(n for t, n in ns if t == "ns")
                claimed.append((prefix + "." if prefix else "") + d.group("name"))
            i = k + 1
            continue
        if doc and l.strip() != "":
            out.extend(doc); doc = []
        out.append(l)
        i += 1
    header = ["/-", f"COMPARATOR CHALLENGE  ({out_mod}): mirror of {src_mod}, generated by",
              "z23_gen_density_challenge.py (QRH zeta23 add-on v2, step B3, v6): Mathlib-only imports, every theorem's proof",
              "replaced by `sorry`, everything else verbatim.", "-/"]
    p = path_of(out_mod)
    p.parent.mkdir(exist_ok=True)
    p.write_text("\n".join(header + out).rstrip("\n") + "\n")
    return claimed

all_claimed = []
for src, out in MIRROR.items():
    c = mirror(src, out)
    if src in CLAIMED:
        all_claimed += c
    print(f"{out}: {len(c)} theorems mirrored" + (" (claimed)" if src in CLAIMED else ""))
Path("MNFChallengesD/All.lean").write_text(
    "/- COMPARATOR CHALLENGE (MNFChallengesD.All): the top mirror; imports every mirror module. -/\n"
    + "\n".join(f"import {m}" for m in MIRROR.values()) + "\n")
cfg = {"challenge_module": CHALLENGE_MODULE, "solution_module": SOLUTION_MODULE, "theorem_names": all_claimed,
       "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"], "enable_nanoda": True}
Path("MNFChallengesD/Density.json").write_text(json.dumps(cfg, indent=2) + "\n")
audit = ["/- Audit of the density layer on the zeta23 tree: axiom reports and printed statements for every",
         "   theorem the Comparator challenge names. Compiled by z23_density_report.sh with plain `lean`,",
         "   sandboxed, against the tree Comparator built. -/", f"import {SOLUTION_MODULE}", ""]
audit += [f"#print axioms {n}" for n in all_claimed] + [""] + [f"#check @{n}" for n in all_claimed]
Path("MNF_AuditDensity.lean").write_text("\n".join(audit) + "\n")
print(len(all_claimed), "theorems listed in MNFChallengesD/Density.json; MNF_AuditDensity.lean written")
