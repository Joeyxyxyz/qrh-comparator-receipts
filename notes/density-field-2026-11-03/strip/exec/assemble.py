#!/usr/bin/env python3
# Assemble StripDensity.lean from the node files (A1.lean carries verbatim copies of every
# upstream node; C.lean supplies the one lemma A1 does not carry).
import re, sys, os

EXEC = os.path.dirname(os.path.abspath(__file__)) + "/.."
A1 = open(f"{EXEC}/A1/A1.lean", encoding="utf-8").read().split("\n")
C = open(f"{EXEC}/C/C.lean", encoding="utf-8").read().split("\n")

def sl(lines, a, b):  # inclusive, 1-indexed
    out = []
    for l in lines[a - 1:b]:
        if l.startswith("/-! ### "): l = "/-! #### " + l[8:]
        elif l.startswith("/-! ## "): l = "/-! ### " + l[7:]
        out.append(l)
    return "\n".join(out)

HEADER = r'''/-
═══════════════════════════════════════════════════════════════════════
ZETA23 — A ZERO-DENSITY ESTIMATE WITH A POWER SAVING (SINGLE-WINDOW FORM)
(StripDensity.lean)
[PROVED | this tree]  No `sorry`; axioms `[propext, Classical.choice, Quot.sound]`
(`#print axioms` for every theorem at the end of the file).
═══════════════════════════════════════════════════════════════════════
Written 2026-11-03 on the zeta23 tree (Lean v4.33.0-rc2, Mathlib 51e6992e), on top of
Zeta23/BL/BohrLandauPartial.lean, Zeta23/BL/BohrLandauClosure.lean (the sharp approximate
formula `BLClosure.zeta_approx_sharp`), Zeta23/BL/JensenDisc.lean, and MNF/RH (`zeta_order`,
`zerosIn`, `is_nontrivial_zero`).

WHAT IS PROVED.  For every `1/2 < σ₁` and `σ₁ − 1/2 < δ ≤ 1/2` there is a constant `C` with

  `NRight δ T ≤ C · T ^ (1 − (2σ₁ − 1)² / (2σ₁)) · (1 + log T) ^ 3`   for all `T ≥ 2`

(`density_single_window`), where `NRight δ T = Zeta23.BL.NRight δ T` (same definition body as
`MNF.RH.NRight`) counts, with multiplicity, the nontrivial zeros `ρ` of ζ with `0 < Im ρ ≤ T`
and `Re ρ − 1/2 ≥ δ`.  The exponent is `1 − (2σ₁ − 1)²/(2σ₁)`: at `σ₁ = 3/4` the count is
`O(T^{5/6} (log T)^3)`; as `σ₁ → 1/2⁺` the saving is `4δ²/(1 + 2δ) ≈ 4δ²`.  This sharpens the
receipted Bohr–Landau bound `NRight δ T = O(T)` (`Zeta23.BL.bohrLandau_full`) to a power
saving: the proportion of zeros in `(T, 2T]` at distance `≥ δ` from the line is `≤ T^{−c}`
rather than `≤ C`.

THE METHOD is Carlson's (1920), with a weaker exponent than Carlson's `4σ₁(1 − σ₁)`: the
mollified function `f_X = ζ · M_X`, `M_X(s) = Σ_{n ≤ X} μ(n) n^{−s}`, is averaged on Jensen
discs centred `2 + it` (the disc machinery of BohrLandauPartial.lean), the circle averages of
`log ‖f_X‖` are majorised by `Leps ε f_X = ½ log(ε² + ‖f_X‖²)` and then, through Jensen's
inequality for the concave `log`, by window mean squares of `‖f_X‖` on vertical segments;
those mean squares come from the product Dirichlet polynomial `S_N · M_X` (Montgomery–Vaughan,
`M1.dirichlet_meanSquare_le`) plus the sharp approximate-formula remainder, with the divisor
bound `Σ_{m ≤ Y} d_X(m)² ≤ Y (1 + log X)³` controlling the coefficients.  One approximate
formula of length `N ≈ T` is used on the single window `[3, T + 3]`; this is what costs the
exponent (Carlson's `4σ₁(1 − σ₁)` needs `N ≈ t` dyadically — not done here).  Multiplicativity
of ζ enters only through `μ * ζ = 1` in the mollifier, and buys a power, not a band.

WHAT THIS IS NOT.  Nothing here touches `MNF.RH.SpectralGapHyp`, nothing here excludes a
single zero, and nothing here says anything about zeros closer than δ to the line: the result
is a *count* of zeros off the line, strictly weaker than any zero-free strip, and not known to
imply anything about one.  Nothing here uses the 7/8 theorem.  A linear saving `1 − c(σ₁ − 1/2)`
(Ingham) is out of reach of this route (it needs a fourth moment not on the tree).

FILE LAYOUT.  The DEFINITIONS block (`Mx`, `fz`, `cm`, `dX`, `Leps`, `NSigma`) is the frozen
block of the plan, copied verbatim; the `open`s before it only resolve `zeta_order`,
`circleAverage` and `Rout/rin/hwin` and are not part of any definition body.  Besides the frozen
block, the section "Exponent arithmetic" introduces seven auxiliary real constants (`E0gen`,
`Egen`, `Esingle`, `K1c`, `Ebarc`, `CMc`, `Ksingle`) that name the error terms; they occur in the
statements of that section and of `count_le_Egen` only, not in `density_single_window`, and a
challenge file must mirror them verbatim (or they can be inlined).  `NRight` is always written
`Zeta23.BL.NRight`, since `open MNF.RH` (needed for the frozen `NSigma` body) would make the
bare name ambiguous with `MNF.RH.NRight`.  Sections, by content: centre bound; product
polynomial; divisor sum; partial summation; window mean squares; mollifier zero orders; Jensen
discs; the `Leps` majorant; integrability and Fubini; count-to-integral; count-to-mean-square;
exponent arithmetic; geometric factor; assembly.
-/
import Zeta23.BL.BohrLandauClosure

set_option lang.lemmaCmd true

open MNF.RH
open Real (circleAverage circleAverage_def)
open scoped Real
open Zeta23.BL (Rout rin hwin)
'''

parts = []
parts.append(HEADER)
parts.append(sl(A1, 40, 56))            # frozen block (namespace + opens + six defs)
parts.append("\n/-! ## END of the frozen DEFINITIONS block -/\n")

parts.append("\n/-! ## Analyticity of `M_X`, `f_X`, and the centre bound on `Re s ≥ 2` -/\n")
parts.append("section Centre\n")
parts.append(sl(A1, 62, 319))
parts.append("")
parts.append(sl(C, 308, 319))           # log_norm_fz_le_of_two_le_re
parts.append("")
parts.append(sl(A1, 755, 773))          # norm_sq_fz_le_of_two_le_re
parts.append("\nend Centre\n")

parts.append("\n/-! ## The product polynomial `S_N · M_X` and its coefficients -/\n")
parts.append("section ProductPolynomial\n")
parts.append(sl(A1, 1106, 1181))
parts.append("\nend ProductPolynomial\n")

parts.append("\n/-! ## The divisor-sum bound `Σ_{m ≤ Y} d_X(m)² ≤ Y (1 + log X)³` -/\n")
parts.append("section DivisorSum\n")
parts.append(sl(A1, 1185, 1386))
parts.append("\nend DivisorSum\n")

parts.append("\n/-! ## Partial summation with generic weights -/\n")
parts.append("section PartialSummation\n")
parts.append(sl(A1, 1390, 1644))
parts.append("\nend PartialSummation\n")

parts.append("\n/-! ## Window mean squares of `S_N · M_X`, `(ζ − S_N) · M_X` and `f_X` -/\n")
parts.append("section Windows\n")
parts.append(sl(A1, 1648, 1682))        # W1
parts.append("")
parts.append(sl(A1, 1685, 1793))        # W2
parts.append("")
parts.append(sl(A1, 1796, 1811))        # open Zeta23.BL + W0
parts.append("")
parts.append(sl(A1, 1817, 1841))        # W3
parts.append("")
parts.append(sl(A1, 1843, 2018))        # W5
parts.append("")
parts.append(sl(A1, 2020, 2145))        # W4
parts.append("\nend Windows\n")

parts.append("\n/-! ## Zero orders: `zeta_order ρ ≤ divisor (f_X) ρ` -/\n")
parts.append("section MollifierOrder\n")
parts.append(sl(A1, 323, 448))
parts.append("\nend MollifierOrder\n")

parts.append("\n/-! ## Jensen's disc inequality for `f_X` -/\n")
parts.append("section JensenDisc\n")
parts.append(sl(A1, 452, 505))
parts.append("\nend JensenDisc\n")

parts.append("\n/-! ## The majorant `Leps ε f = ½ log(ε² + ‖f‖²)` -/\n")
parts.append("section LepsMajorant\n")
parts.append(sl(A1, 509, 551))
parts.append("")
parts.append(sl(A1, 777, 847))
parts.append("\nend LepsMajorant\n")

parts.append("\n/-! ## Integrability of `Leps ε (f_X)` on circles and segments; Fubini -/\n")
parts.append("section Integrability\n")
parts.append(sl(A1, 555, 612))
parts.append("")
parts.append(sl(A1, 851, 864))
parts.append("")
parts.append(sl(A1, 866, 883))
parts.append("\nend Integrability\n")

parts.append("\n/-! ## From the zero count to the integral of the circle averages -/\n")
parts.append("section CountToIntegral\n")
parts.append(sl(A1, 616, 750))
parts.append("\nend CountToIntegral\n")

parts.append("\n/-! ## From the zero count to the window mean squares -/\n")
parts.append("section CountToMeanSquare\n")
parts.append(sl(A1, 888, 1096))
parts.append("\nend CountToMeanSquare\n")

parts.append("\n/-! ## Exponent arithmetic -/\n")
parts.append("section ExponentArithmetic\n")
parts.append(sl(A1, 2155, 2812))
parts.append("\nend ExponentArithmetic\n")

parts.append("\n/-! ## The geometric factor `2 hwin log(Rout/rin)` -/\n")
parts.append("section GeometricFactor\n")
parts.append(sl(A1, 2820, 2864))
parts.append("\nend GeometricFactor\n")

parts.append("\n/-! ## Assembly: the single-window zero-density estimate -/\n")
parts.append("section Assembly\n")
parts.append(sl(A1, 2872, 3061))
parts.append("\nend Assembly\n")
parts.append("\nend Zeta23.Density\n")

text = "\n".join(parts)

# ---------------------------------------------------------------- comment rewriting
NAMES = [
    ("G7w", "`count_le_integral_fz_window`"),
    ("C1'", "`analyticOnNhd_fz`"), ("C1", "`analyticOnNhd_Mx`"),
    ("C2a", "`tail_inv_sq_le`"), ("C2b", "`fz_sub_one_eq`"), ("C2c", "`norm_fz_sub_one_le`"),
    ("C2d", "the centre bound"),
    ("G1a", "`log_norm_le_Leps`"), ("G1b", "`concaveOn_half_log_add`"),
    ("G1c", "`segment_average_Leps_le`"), ("G1d", "`half_log_le_half`"),
    ("G3", "`circleAverage_log_norm_le_Leps`"),
    ("G4a", "`Mx_ne_zero_of_le_re`"), ("G4b", "`analyticOrderAt_Mx_ne_top`"),
    ("G4'", "`finset_sum_zeta_order_le_finsum_divisor_fz`"), ("G4", "`zeta_order_le_divisor_fz`"),
    ("G5'", "`count_window_le_fz`"), ("G5", "`count_finset_le_fz`"),
    ("G6", "`integral_circleAverage_Leps_eq_swap`"), ("G7", "`count_le_integral_fz`"),
    ("G8", "`geom_lower`"),
    ("P1", "`S_mul_Mx_eq`"), ("P2", "`cm_eq_of_le`"), ("P3", "`abs_cm_le`"),
    ("E1a", "`card_filter_dvd_dvd_le`"), ("E1b", "`gcd_le_sum_dvd`"),
    ("E1c", "`sum_div_of_dvd_le`"), ("E1d", "`sum_gcd_div_le`"), ("E1", "`sum_dX_sq_le`"),
    ("D0'", "`sum_mul_le_of_partial_sums_tail`"), ("D0", "`sum_mul_le_of_partial_sums`"),
    ("D1", "`tail_sum_le`"), ("D2", "`weight_sum_le`"),
    ("W0", "`norm_add_sq_le_eta`"), ("W1", "`integral_window_eq`"),
    ("W2", "`meanSquare_prodPoly`"), ("W3", "`norm_Mx_le`"),
    ("W4", "`meanSquare_fz_window`"), ("W5", "`meanSquare_B_window`"),
    ("A0", "`count_le_meanSquare_fz`"), ("A1", "`density_single_window`"),
    ("A2", "`exponent_single`"),
]
LABEL = r"(?:C1'|C1|C2[a-d]|G1[a-d]|G3|G4[ab]|G4'|G4|G5'|G5|G6|G7|G8|P[1-3]|E1[a-d]|E1|D0'|D0|D1|D2|W[0-5]|A[0-2])"

SPECIFIC = [
    ("`K, T₀` from A2's", "`K, T₀` from"),
    ("A2's `exponent_single`", "`exponent_single`"),
    ("A0's window mean-square hypothesis", "the window mean-square hypothesis `hMS` of `count_le_meanSquare_fz`"),
    ("A0's `hMS`", "the hypothesis `hMS` of `count_le_meanSquare_fz`"),
    ("`hMS` of A0", "`hMS` of `count_le_meanSquare_fz`"),
    ("the right-hand side of A0", "the right-hand side of `count_le_meanSquare_fz`"),
    ("The W4 excess", "The window mean-square excess"),
    ("The W4 right-hand side", "The right-hand side of `meanSquare_fz_window`"),
    ("the W4 right-hand side", "the right-hand side of `meanSquare_fz_window`"),
    ("The full A0 error", "The full error term of the count-to-mean-square bound"),
    ("the A0 error", "the error term"),
    ("A1 instantiates", "the assembly instantiates"),
    ("(A0 + W4)", "(`count_le_meanSquare_fz` + `meanSquare_fz_window`)"),
    ("G6 swap", "Fubini swap `integral_circleAverage_Leps_eq_swap`"),
    ("product integrability of G6", "product integrability `integrable_Leps_circleMap_prod_restrict`"),
    ("-- G7 (window form)", "-- the count-to-integral bound, window form"),
    ("centre bound C2d", "centre bound"),
    ("The Stage-4 core", "The assembly core"),
    ("(plan item A2)", ""),
    ("Glue for A1:", "Glue for the assembly:"),
    ("(the plan's statement, `STRIP_PLAN.md` §(C) Stage 2)", "(`NRight` form)"),
    ("(the plan's statement, `STRIP_PLAN.md` §(C) Stage 3)", "(`NRight` form)"),
    (" (the plan's \"window parameters abstracted from the start\")", ""),
    ("the plan's convention", "the convention of this file"),
    ("the plan's statement shape", "the statement shape"),
    ("plan's signature", "signature"),
    ("(see the file header)", "(the single-window error term)"),
    ("SCRATCH-ONLY.", "Auxiliary constant (outside the frozen definitions block)."),
    ("### Scratch-only definitions (inline in the final module)", "### Auxiliary constants (outside the frozen definitions block)"),
    ("**A1 (`density_single_window`).**", ""),
    ("restricted to C2b:", "restricted to `fz_sub_one_eq`:"),
    ("(the centre bound + G1d)", "(`norm_sq_fz_le_of_two_le_re` + `half_log_le_half`)"),
    ("(C2d + G1d)", "(`norm_sq_fz_le_of_two_le_re` + `half_log_le_half`)"),
    ("(C2d `‖fz X s‖² ≤ 1 + π²/(2X)` and G1d)", "(`norm_sq_fz_le_of_two_le_re` and `half_log_le_half`)"),
    ("(`‖fz X (2 + it)‖ ≥ 1/2`, C2d)", "(`fz_lower_two`)"),
    ("non-zero at the centre by C2d", "non-zero at the centre by `fz_two_add_ne_zero`"),
    ("/-- ** ", "/-- "),
    ("/-- **", "/-- "),
    ("The main statement  -/", "The main statement -/"),
    ("the binder `{σ₁ δ : ℝ}` of G5' and G7", "every binder `{σ₁ δ : ℝ}` below"),
]

def fix_comment(line):
    for a, b in SPECIFIC:
        line = line.replace(a, b)
    # drop leading item labels in docstrings / headers
    line = re.sub(r"^(\s*/--\s*)(?:\*\*)?" + LABEL + r"(?:\*\*)?[:.]\s*", r"\1", line)
    line = re.sub(r"^(/-! #+\s*)" + LABEL + r"(?: \([^)]*\))?\s*[.:—–-]?\s*", r"\1", line)
    line = re.sub(r"^(\s*/--\s*)" + LABEL + r", ", r"\1", line)           # "G5, divisor form"
    line = re.sub(r"^(\s*/--\s*)" + LABEL + r" in the ", r"\1The ", line)  # "G7 in the Carlson-stage shape"
    line = re.sub(r" \(`Density/[A-Za-z]+\.lean`\)", "", line)
    # remaining mid-text labels -> lemma names
    for lab, rep in NAMES:
        line = re.sub(r"(?<![\w`'])" + re.escape(lab) + r"(?![\w'])", rep, line)
    return line

out = []
in_block = False
for line in text.split("\n"):
    s = line.strip()
    is_comment = in_block or s.startswith("--") or s.startswith("/-")
    if is_comment:
        line = fix_comment(line)
    if "/-" in s and "-/" not in s.split("/-", 1)[1]:
        in_block = True
    if "-/" in s:
        in_block = False
    out.append(line)
text = "\n".join(out).replace("/-- ** ", "/-- ")

# capitalise docstrings/headers that now start lowercase after a stripped label (cosmetic);
# never inside the frozen block
marker = "/-! ## END of the frozen DEFINITIONS block -/"
head, tail = text.split(marker, 1)
tail = re.sub(r"(/--\s+|/-! #+\s+)([a-z])", lambda m: m.group(1) + m.group(2).upper(), tail)
tail = tail.replace("/-! ### The geometric factor -/\n\n", "")
tail = tail.replace("/--  Zero-density", "/-- Zero-density")
text = head + marker + tail

# ---------------------------------------------------------------- #print axioms
names = re.findall(r"^(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'!?]*)", text, flags=re.M)
seen = []
for n in names:
    if n not in seen:
        seen.append(n)
text += "\n" + "\n".join(f"#print axioms Zeta23.Density.{n}" for n in seen) + "\n"

open(f"{EXEC}/merged/StripDensity.lean", "w", encoding="utf-8").write(text)
print("declarations:", len(seen))
