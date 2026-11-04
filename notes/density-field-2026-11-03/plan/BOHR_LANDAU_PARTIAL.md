# Bohr–Landau beyond 1/6 — what the plan-execution workflow proved (2026-11-03)

Ten agents executed the DAG of `BOHR_LANDAU_PLAN.md` (nodes J0/J2/J3, M1, M2, M3a, J4/J5, M3, J6/J7,
J8/J9, M4/M5) and a merge agent assembled the result: `Zeta23/BL/BohrLandauPartial.lean` on the
zeta23 tree, 2172 lines, 145 declarations, no `sorry`, every one with axioms exactly
`[propext, Classical.choice, Quot.sound]` (I re-checked the headline ones myself: `plan/AuditPartial`
in this folder's logs). The MNF-vocabulary corollaries are `MNF/RH/DensityPartial.lean`.

## The theorems (kernel-checked, unconditional)

| Lean name | statement |
|---|---|
| `Zeta23.BL.M3.meanSquareUnif_explicit` | for 2/3 ≤ σ₁ < 1, every σ ≥ σ₁ and T ≥ 1: ∫₁ᵀ ‖ζ(σ+it)‖² dt ≤ C(σ₁)·T with C(σ₁) = 4(1 + 1/(2σ₁−1)) + 208(1 + 4/(2−2σ₁)) + 17 + 4(1+1/σ₁)² |
| `Zeta23.BL.M45.meanSquare_strip_of` | the sorried statement `meanSquare_strip` of BohrLandau.lean, for 2/3 ≤ σ ≤ 1 (∫₀ᵀ form). At σ = 1 it holds only because ‖ζ(1+it)‖² is not integrable at t = 0 (`not_intervalIntegrable_zeta_one_sq`) and Mathlib's integral of a non-integrable function is 0; the genuine σ = 1 content is `meanSquare_one_from_one` on [1, T] |
| `Zeta23.BL.rightHalf_of_meanSquareUnif` | for 1/2 < σ₁ < 1: a uniform O(T) mean square on Re s ≥ σ₁ gives N_right(δ; T) = O(T) for every δ > σ₁ − 1/2 (Jensen on discs centred 2 + it, radius 2 − σ₁, averaged in t; Fubini; log(1+x) ≤ x) |
| `Zeta23.BL.rightHalf_gt_sixth` | **for every δ > 1/6, the zeros with Re ρ − 1/2 ≥ δ, 0 < Im ρ ≤ T, counted with multiplicity, number ≤ C·T for T ≥ 2** |
| `Zeta23.BL.bohrLandau_gt_sixth` | **the same for \|Re ρ − 1/2\| ≥ δ, δ > 1/6** (reflection) |
| `MNF.RH.reservoirDensity_gt_sixth` | for every δ > 1/6: N_off(δ; 0,T) ≤ ε·N(0,T) eventually — density one within δ of the line, no hypothesis |
| `MNF.RH.onLineDensityOne_of_gap_gt_sixth` | a gap at any Δ > 1/6 gives density one on the line, no other hypothesis |

## What it is and is not

- It is the classical Bohr–Landau theorem restricted to δ > 1/6, formalized from scratch on top of
  the tree's approximate formula `Zeta0EqZeta` (PNT+ port), the weighted Hilbert inequality
  `Zeta23.MV.mvDiag_thirteen`, Mathlib's Jensen formula, and `zeta_lower_bound_two`.
- The restriction to δ > 1/6 is a limitation of the naive error term ‖s‖N^{−σ}/σ in the tree's
  approximate formula (the window 1/σ ≤ a ≤ 1/(2−2σ) for N = T^a is non-empty iff σ ≥ 2/3), not a
  theorem about where it fails; the sharper approximation (first-derivative test or a second
  Euler–Maclaurin step, plan §M6) would extend it to every δ > 0.
- Nothing here is about RH or the gap hypothesis; `onLineDensityOne_of_gap_gt_sixth` only moves
  the "Bohr–Landau" binder of the earlier density theorem into the proved range.

## Files

`zeta23-tree/Zeta23/BL/BohrLandauPartial.lean`, `zeta23-tree/MNF/RH/DensityPartial.lean`; the
per-node files and the merge agent's compile log are under `plan/plan-exec/`.
