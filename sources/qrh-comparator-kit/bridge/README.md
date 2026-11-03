# The MNF bridge, in two files

Both files are for OpenAI's Lean environment (Lean 4.34.1, Mathlib `d13f23b7`). They are the
kit's last step, run only after Comparator has passed OpenAI's theorem.

## `MNF_Bridge78.lean`

The bridge written for the corpus on 2026-10-07, brought to OpenAI's Lean version. The port
needed no change of substance (one deprecated tactic call was replaced), and this version
compiles unchanged at the corpus pin as well, so it can replace the earlier file there. It
imports Mathlib only. The 7/8 theorem appears in it as an explicit hypothesis,

```lean
def ZeroFreeRightOf (θ : ℝ) : Prop := ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0
```

at `θ = 7/8`, and every theorem that needs it says so in its signature. Nothing in this file
depends on OpenAI. One theorem was added: `nontrivial_zero_re_mem`, which says that under the
hypothesis every nontrivial zero has real part between 1/8 and 7/8.

The countermodels of sections 3 and 8 (`structural_inputs_insufficient`, `analytic_no_go`,
`euler_type_no_go`) need no hypothesis at all. They are the part of the file that says what a
proof of the remaining strip cannot rely on.

## `MNF_Bridge78_Unconditional.lean`

Imports the file above and OpenAI's `OAI.NumberTheory.DirichletL.Nonvanishing`. It contains one
term that turns OpenAI's theorem into `ZeroFreeRightOf (7/8)`, and six one-line theorems that
apply the bridge to it. No tactic, no automation: if the file above compiles and OpenAI's
theorem has the pinned statement, this file compiles.

What comes out, with no hypothesis left in the signature:

| Theorem | Says |
|---|---|
| `zeroFree_seven_eighths` | OpenAI's theorem, in the bridge's vocabulary |
| `nontrivial_zero_re_mem_unconditional` | every nontrivial zero has 1/8 ≤ Re ≤ 7/8 |
| `shifted_bounded_three_eighths_unconditional` | the shifted zero spectrum lies in [-3/8, 3/8] |
| `riemannHypothesis_iff_gap_unconditional` | RH ⟺ the MNF gap, at any threshold Δ > 3/8 |
| `riemannHypothesis_iff_remaining_strip_unconditional` | RH ⟺ no zeros with 1/2 < Re s ≤ 7/8 |
| `zetaZeros_satisfies_structural_inputs_unconditional` | the zero set meets every hypothesis of the structural no-go |
| `euler_type_no_go_unconditional` | ζ·Q is zero-free right of 7/8 and still has a zero in the remaining strip |

None of these is the Riemann Hypothesis, and none of them moves the gap hypothesis from open to
proved. The fourth and fifth say precisely what remains.

## How phase 8 checks them

`scripts/08_bridge.sh` compiles the first file on its own (so its proofs are checked in the same
small environment they were written in), then the second against it and against the tree
Comparator has just checked. Both compiles run inside the sandbox, in a unit that may not open
AF_UNIX sockets, like Comparator's own builds; the first may write its compiled file into one
scratch folder, the second may write nowhere. The phase requires exit
code 0, no errors, no `sorry`, and an axiom report for each of the 21 audited theorems listing
nothing beyond `propext`, `Classical.choice`, `Quot.sound`. It also prints the statements as
Lean shows them and says whether they equal `expected_statements.txt` character for character;
a difference in form is noted in the report and is not a failure, because the theorems are
fixed by the source files. The three files are pinned by sha256 in `PINS.env`.

This is an ordinary compile, not a Comparator run. It is as strong as the PASS it stands on,
and the phase refuses to run without one.

## What was compiled when the kit was written

- `MNF_Bridge78.lean`: with Lean 4.34.1 and Mathlib `d13f23b7` (OpenAI's versions) and,
  unchanged, with Lean 4.24.0 and Mathlib `f897ebcf` (the corpus pin). No warnings at either;
  all 14 axiom reports standard.
- `MNF_Bridge78_Unconditional.lean`: with OpenAI's versions, against a stand-in for OpenAI's
  theorem, since the real proof could not be built on that machine. `expected_statements.txt`
  is what Lean printed there.

## Where these statements live

Only inside OpenAI's tree, with OpenAI's Lean and Mathlib. The corpus is pinned to Lean 4.24.0
and Mathlib `f897ebcf`; OpenAI's proof does not exist at that pin, so there
`MNF_Bridge78.lean` keeps the hypothesis. A PASS changes the hypothesis's standing, from
"published by OpenAI" to "published by OpenAI and independently checked by Comparator on
(date), receipt attached".
