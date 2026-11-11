# Review of WORK/paper.md: mathematical exposition

Reviewer lens: the mathematics read as a number theorist would read it. Reviewed 2026-11-10
against `WORK/paper.md` (662 lines). Nothing outside WORK was modified; the paper was not edited.

Abbreviations: `V6` = `/home/joeyxyxyz/repos/qrh-comparator-receipts/sources/qrh-zeta23-addon-v6`,
`NOTES` = `/home/joeyxyxyz/repos/qrh-comparator-receipts/notes/density-field-2026-11-03`,
`R11` = `WORK/extracted/qrh-zeta23-density-v6-receipt/density-v6`.
Reviewer scripts (pure Python, no dependencies): `WORK/review/_mathexp/gue_sd.py`,
`gue_cdf.py`, `exponents.py`.

## Verdict

One major finding (a wrong numerical constant) and twelve minor ones. No proof sketch is wrong.
The mathematics of sections "The density layer" and "A zero-density estimate, the displacement
bound and the pair measure" agrees with the Lean statements in `R11/audit.out` and with the
plans, and the comparisons with Carlson, Ingham, Littlewood and Selberg are arithmetically right.

## What was checked and found correct

- Zero-density exponent. With theta = (2 sigma_1 - 1)/(2 sigma_1) and
  kappa = (2 sigma_1 - 1)^2/(2 sigma_1): theta(1 - 2 sigma_1) = -kappa (diagonal),
  (2 - 2 sigma_1) + theta(2 - 2 sigma_1) - 1 = -2 kappa (off-diagonal),
  kappa + theta(2 - 2 sigma_1) + (1 - 2 sigma_1) = -kappa (the eta-weighted remainder),
  theta >= kappa (center term), checked exactly at four values of sigma_1
  (`_mathexp/exponents.py`); these are the identities quoted from `V6/Zeta23/Density/StripDensity.lean`
  in `WORK/facts/density.md` 5b. At sigma_1 = 3/4: 5/6 here, 3/4 Carlson, 3/5 Ingham.
  Carlson's balance X = T^(2 sigma_1 - 1) gives saving (2 sigma_1 - 1)^2, as the paper says.
  The supremum of the saving for a given sigma is (2 sigma - 1)^2/(2 sigma) = 4 delta^2/(1 + 2 delta)
  and is not attained (strict sigma_1 < sigma), as the paper says.
- Order of the exponents on (1/2, 1), on a grid of 999 rational points: Lewko's A(sigma)(1 - sigma)
  (the four-piece curve of `WORK/facts/literature.md`) < exponent here; Ingham < Carlson < exponent here.
- Layer cake and 3/5: head delta_0 N(T) << delta_0 T log T, tail (2/3) A delta_0^(-3/2) T + (B/2) T,
  balance at delta_0 = (log T)^(-2/5), both of order T (log T)^(3/5); general rule (a - 1)/a at a = 5/2.
  The exponents in `reservoirMass_le_rpow` and `bohrLandau_explicit` are real powers in the source
  (`V6/MNF/RH/ReservoirMass.lean`: "(A * δ ^ (-(5/2 : ℝ)) + B) * T").
- Real zeros: the one-term Euler-Maclaurin identity, |J| <= 1/(2 sigma), and
  1/2 + sigma/(1 - sigma) = 1/(1 - sigma) - 1/2 > 1/2.
- Jensen disks: geometry (R = 2 - sigma_1 < 3/2 <= t, so the pole is missed), the window
  [gamma - h, gamma + h] inside [3, T + 3] for 4 < gamma <= T, center term T log 3 from
  |zeta(2 + it)| >= 1/3, the majorant (1/2) log(1 + |zeta|^2) <= (1/2)|zeta|^2: agree with
  `Zeta23.BL.count_le_integral` and `geom_facts` as printed in `R11/audit.out`.
- Reflection: N_off = 2 N(1/2 + delta, T) for delta > 0 (`MNF.RH.NOff_eq_right_add_left`,
  `NLeft_eq_NRight`), the signed sum, and the pair-sum bound P <= N_ne N + N_0 N_ne with
  5/9 = (1/3)(2 - 1/3); the counterexample 10 > 8 (and 10 <= 12 for the corrected bound).
- Montgomery-Vaughan: the form with 26 = 2 * 13 is the Lean statement of
  `M1.dirichlet_meanSquare_le`; the window 1/sigma_1 <= a <= 1/(2 - 2 sigma_1), nonempty exactly for
  sigma_1 >= 2/3, is right.
- Steps 1 to 4 (Euler-Maclaurin, B_2 Fourier series, first-derivative test with 4 G(a)/lambda,
  mode bound 8/(pi nu) x^(-sigma-2) under t <= pi x, sharp formula) agree with the Lean statements.
- Selberg: integrating T^(1 - (sigma - 1/2)/4) log T over [1/2, 1] gives at most 4T.
- Numerics: the exact-GUE expected counts 3.4, 11.0, 45.1, 213.0 and the pair count 0.2263 were
  recomputed from the sine-kernel Fredholm determinant (`_mathexp/gue_cdf.py`) and agree.
- Ingham 1940, pages 201-202: confirmed at https://api.crossref.org/works/10.1093/qmath/os-11.1.201 .

## Findings

### 1. MAJOR. The GUE standard deviation is wrong

- Location: "A numerical illustration": "have mean 0.99744, standard deviation 0.3709 (GUE: 0.4221) and minimum 0.2434".
- Problem: 0.4221 is the standard deviation of neither GUE spacing law. The Wigner surmise has
  sqrt(3 pi/8 - 1) = 0.4220; the exact (Gaudin-Mehta) law, which is the GUE reference of every
  other number in this subsection, has 0.4243 (second moment 1.17999, variance 0.17999). The
  value in the notes is a hard-coded string, not a computed number.
- Evidence: `NOTES/numeric/mnf_analysis.py`, line 88:
  `f"(GUE surmise sd = {math.sqrt(3*PI/8 - 1):.4f}, exact GUE sd ~ 0.4221, Poisson sd = 1)")`;
  `NOTES/numeric/mnf_analysis.log`, line 3: "GUE surmise sd = 0.4220, exact GUE sd ~ 0.4221";
  `NOTES/numeric/RESULTS.md`, line 119: "GUE 0.4221, Poisson 1". Reviewer computation
  `WORK/review/_mathexp/gue_sd.py` (Nystrom discretization of det(I - K_sine) on [0, s]):
  "E(0;1) = 0.1702174213791851" (the notes' own check value is "E_2(0;1) = 0.170217"),
  "second moment 1.1799938776918384 variance 0.1799938776918384 sd 0.4242568534412124",
  "surmise sd 0.4220156929501229".
- Fix: replace "(GUE: 0.4221)" by "(Wigner surmise for GUE: 0.4220; exact GUE law: 0.4243)".
  If only numbers computed in the record may be printed, use "(Wigner surmise for GUE: 0.4220)".
  Add to "Errata", under "Found while preparing this paper": "The notes give the GUE standard
  deviation of the normalized spacing as 0.4221 (`numeric/RESULTS.md`); that value is a constant
  typed into `mnf_analysis.py`, and the exact law gives 0.4243 (the Wigner surmise 0.4220)."

### 2. minor. "the most recent improvement" is not Guth-Maynard

- Location: "The zero-density estimate": "and the most recent improvement is due to Guth and Maynard [@guth-maynard]".
- Problem: later improvements exist and are cited in the same paragraph: Tao, Trudgian and Yang
  (January 2025, after Guth and Maynard's May 2024 preprint) announce new zero-density estimates,
  and two of Lewko's 2026 entries are titled as improvements. The fact sheet supports only
  "current record" for the uniform exponent.
- Evidence: `WORK/facts/literature.md`, entry `guth-maynard`: "Cited for: the current zero-density
  record N(σ, T) ≤ T^{30(1−σ)/13+o(1)}; context only."; entry `tao-trudgian-yang`: title "New
  exponent pairs, zero density estimates, and zero additive energy estimates: a systematic
  approach", 28 January 2025; https://arxiv.org/abs/2501.16779 (the abstract lists new zero-density estimates
  for zeta among its results); entry `lewko-density-improved`: "Improved
  zero-density estimates for the Riemann zeta function".
- Fix: "and the sharpest known bound of the form $N(\sigma, T) \le T^{A(1-\sigma)+o(1)}$ uniform in
  $\sigma$, with $A = 30/13$, is due to Guth and Maynard [@guth-maynard]".

### 3. minor. The mean value for sigma > 1/2 is older than Hardy-Littlewood 1918

- Location: "Architecture of the formal proof", Step 5: "This is the $O(T)$ upper bound of the Hardy–Littlewood mean-value theorem [@hardy-littlewood-1918]".
- Problem: the mean value of |zeta(sigma + it)|^2 for fixed sigma > 1/2 is older than 1918: it is
  in Landau's Handbuch (1909), see the evidence, and the theorem formalized in this section dates
  from 1914. A reader who knows the history will take the 1918 attribution for an anachronism. The
  fact sheet did not verify the attribution; it records it as the record's own. (The same wording is in the
  Lean docstring and in DEPOSIT_MAP section 10 ("Hardy–Littlewood's O(T) mean square for every σ₁ > 1/2 (run 9)"); this is a wording choice of the paper, not a change
  to the record.)
- Evidence: `WORK/facts/literature.md`, entry `hardy-littlewood-1918`: "That the σ > 1/2
  mean-square theorem is in this paper is the record's attribution ('Hardy–Littlewood's O(T) mean
  square') and the standard one; not read in the original."; Broucke and Hilberdink,
  https://arxiv.org/pdf/2409.06301 , Remark (iii), on the mean of |zeta(sigma + it)|^2 for
  sigma > 1/2: "either directly as in Landau [16, p. 806] (see also Titchmarsh [22, Lemma 7.2])",
  where [16] is Landau's Handbuch of 1909; `V6/Zeta23/BL/BohrLandauClosure.lean`: "(Titchmarsh §7.2)".
- Fix: "This is the $O(T)$ upper bound in the classical mean-value theorem for fixed
  $\sigma > 1/2$ (Section 7.2 of [@titchmarsh]); the asymptotic formula $\sim \zeta(2\sigma)\,T$ is
  not proved." Then remove `hardy-littlewood-1918` from the References (it is cited nowhere else).

### 4. minor. "does not give" asserts more than is known

- Location: "Counting functions and two notions of density": "The first does not give the second: it places no constraint on zeros off the line whose distance from it tends to zero."
- Problem: `ReservoirDensityOne` is a theorem of the layer, so "the first gives the second" is
  equivalent to `OnLineDensityOne`, which follows from RH and is open. The sentence states as a
  fact that an implication fails when only "is not known" is justified.
- Evidence: `R11/MNF_DENSITY.md`: "MNF.RH.reservoirDensityOne_unconditional : MNF.RH.ReservoirDensityOne";
  `V6/MNF/RH/Density.lean`: "`OnLineDensityOne` is implied by RH and is not known to imply it".
- Fix: "The first is not known to give the second: it places no constraint on zeros off the line
  whose distance from it tends to zero."

### 5. minor. One letter for three constants

- Location: "The displacement of the zeros from the line": "the lower bound for $N(T)$ then gives $D(T) \le A (\log T)^{-2/5} N(T)$" (also "the bound $D(T) \le A\, T (\log T)^{3/5}$ for $T \ge T_0$" and "there are $A, B \ge 0$ with").
- Problem: within eight lines $A$ is the constant of the displacement bound, the constant of the
  explicit Bohr-Landau bound, and the constant of the relative bound. They are three different
  numbers, and the tail estimate "(2/3) A delta_0^(-3/2)" only makes sense for the second.
- Evidence: `V6/MNF/RH/ReservoirMass.lean`: "In the first bound A = C + (2/3)·2A₀ + N(0,4)/2 with
  C = 4A₀' from `Ncount_le_mul_log`" and "the constant of the second bound is 16π·|A|" (each quote joined across a line break).
- Fix: in the paragraph beginning "The input is the Bohr–Landau bound" write
  "there are $A_1, B_1 \ge 0$ with $N_{\mathrm{off}}(\delta, T) \le (A_1\delta^{-5/2} + B_1)\,T$",
  "the tail at most $(\tfrac23 A_1 \delta_0^{-3/2} + B_1/2)\,T$", and
  "then gives $D(T) \le A' (\log T)^{-2/5} N(T)$ with another constant $A'$".

### 6. minor. Sign of the main term

- Location: "The milestone for distances above one sixth": "The Montgomery–Vaughan term and the term $N^{1-s}/(1-s)$ are of order $N^{2-2\sigma_1}$".
- Problem: Steps 1 and 4 and the zero-density section write this term as $N^{1-s}/(s-1)$; the
  tree's form is $-N^{1-s}/(1-s)$. As printed the term has the opposite sign.
- Evidence: `R11/audit.out`, `@BLClosure.zeta_eq_euler_maclaurin`: "BLClosure.S N s + ↑N ^ (1 - s) / (s - 1) - ↑N ^ (-s) / 2";
  `V6/Zeta23/BL/BohrLandauPartial.lean`, line 537: "(-(N:ℂ) ^ (1 - ((σ:ℂ) + t * I))) / (1 - ((σ:ℂ) + t * I))".
- Fix: "The Montgomery–Vaughan term and the term $N^{1-s}/(s-1)$ are of order $N^{2-2\sigma_1}$".

### 7. minor. The third equivalence also uses complex conjugation

- Location: "Degenerate zeros and two equivalences": "the third also needs that no nontrivial zero is real, because the windows see positive ordinates only".
- Problem: a reader asks at once about zeros with negative ordinates, which no window sees either.
  The proof handles them by conjugation; the sentence names only the real zeros.
- Evidence: `V6/MNF/RH/Cube.lean`, lines 483 to 484: "(negative ordinates by conjugation, real zeros
  excluded by `nontrivial_zero_im_ne_zero`)" (joined across the line break).
- Fix: "the third also needs complex conjugation, for the zeros with negative ordinates, and the
  fact that no nontrivial zero is real, because the windows see positive ordinates only".

### 8. minor. Selberg's estimate must be uniform to be integrated

- Location: "The displacement of the zeros from the line": "Selberg's estimate $N(\sigma, T) \ll T^{1 - (\sigma - 1/2)/4} \log T$ [@selberg-1946] gives $O(T)$ on integration over $\sigma$".
- Problem: the integration over sigma needs the implied constant to be independent of sigma;
  the paper does not say that the estimate is uniform.
- Evidence: `WORK/facts/literature.md`, entry `selberg-1946`: "N(σ, T) ≪ T^{1 − (σ − 1/2)/4} log T
  uniformly for 1/2 ≤ σ ≤ 1 (Theorem 1 there)".
- Fix: "Selberg's estimate $N(\sigma, T) \ll T^{1 - (\sigma - 1/2)/4} \log T$, uniform for
  $1/2 \le \sigma \le 1$ [@selberg-1946], gives $O(T)$ on integration over $\sigma$".

### 9. minor. `Zeta0EqZeta` is an identity, not an approximate formula

- Location: "Architecture of the formal proof": "From the tree the proof takes the approximate formula `Zeta0EqZeta`"; and "The milestone for distances above one sixth": "but only the tree's approximate formula, and reached".
- Problem: Step 1 and the section on real zeros use `Zeta0EqZeta` as an exact Euler-Maclaurin
  representation. "Approximate formula" is the name of Step 4's result, so the two are confused.
- Evidence: `V6/Zeta23/BL/BohrLandauPartial.lean`, lines 534 to 541: `zeta_eq_four_terms` states
  "riemannZeta ((σ:ℂ) + t * I) = ..." and is proved by "rw [← Zeta0EqZeta (N := N) (by omega) (by simp [hσ]) (s_ne_one ht)]";
  the paper itself, "No real zeros in the interval (0,1)": "one term of Euler–Maclaurin, the tree's `Zeta0EqZeta` at $N = 1$".
- Fix: "From the tree the proof takes the Euler–Maclaurin representation `Zeta0EqZeta`"; and
  "but only the tree's bound for the Euler–Maclaurin tail, and reached".

### 10. minor. What a verification up to a height would add

- Location: "What would strengthen the work": "would turn the illustration into a theorem for that range".
- Problem: the illustration is about spacing statistics; a verification that the zeros up to a
  height are simple and on the line would certify the list of zeros, not the comparison with GUE.
- Evidence: the paper, "A numerical illustration": "They concern spacings of ordinates on the
  critical line, not real parts" and "The ordinates are uncertified, and the completeness of the
  list rests on the count above, not on a Turing-style argument."
- Fix: "would replace the uncertified list of zeros behind the illustration by a theorem for that
  range (the comparison with GUE would remain statistical)".

### 11. minor. Symbols used twice

- Location: "Architecture of the formal proof", Step 1: "where $P=(B_2(\{u\})-\tfrac16)/2$ is the continuous periodic antiderivative of $\psi$".
- Problem: *Notation* reserves $P(T)$ for the pair sum; Step 1 uses $P$ for a periodic function.
  Likewise $N$ is the length of a Dirichlet polynomial in the sketches and, with arguments, a
  counting function ($N(T)$, $N(\sigma, T)$), sometimes in one paragraph (Step 6 and the milestone).
- Evidence: the paper, *Notation*: "$P(T)$ is the sum of $m(\rho)\,m(\rho')$ over ordered pairs of
  distinct zeros"; `V6/Zeta23/BL/BohrLandauClosure.lean`: "P = (B₂per − 1/6)/2".
- Fix: in Step 1 write $\psi_2$ for the periodic function ("replaces $\psi(u)\,u^{-s-1}$ by
  $(s+1)\psi_2(u)\,u^{-s-2}$, where $\psi_2=(B_2(\{u\})-\tfrac16)/2$ ..."), and add to *Notation*:
  "In the proof sketches $N$ without an argument is the length of a Dirichlet polynomial."

### 12. minor. Appendix B lists the elementary mean value, not the one the proof uses

- Location: "Appendix B. Principal Lean theorems": "| `DPMV.dirichlet_mean_value` | `Zeta23/BL/DPMV.lean` |".
- Problem: the row gives the form with the off-diagonal bounded term by term, which is not
  enough for the mean square of zeta; the proof uses the Montgomery-Vaughan form
  `M1.dirichlet_meanSquare_le` (Step 5), which the table omits.
- Evidence: `WORK/facts/density.md` 4.4: "This is the elementary form with the off-diagonal
  bounded term by term; the Montgomery-Vaughan form used later in the mean square of zeta is a
  different theorem, `M1.dirichlet_meanSquare_le` in `BohrLandauPartial.lean`".
- Fix: append to the reading of that row: "(the elementary form; the mean square of $\zeta$ uses
  the Montgomery–Vaughan form `M1.dirichlet_meanSquare_le`, Step 5 of *Architecture of the formal proof*)".

### 13. minor. "Jensen's inequality" names two different results

- Location: "Architecture of the formal proof", Step 6: "Jensen's inequality at each $t$, integrated over $3\le t\le T+3$ for $T\ge4$"; "The zero-density estimate", item 1: "so Jensen's inequality for $f_X$ counts them".
- Problem: here the phrase means the zero-counting inequality that follows from Jensen's formula;
  four lines below item 1 it means the convexity inequality ("Jensen's inequality for the concave
  logarithm").
- Evidence: `V6/Zeta23/BL/JensenDisc.lean`: "have jensen := h₁f'.circleAverage_log_norm hR.ne' h₂f"
  (Mathlib's Jensen formula); the paper, item 5: "Jensen's inequality for the concave logarithm".
- Fix: Step 6: "The disk inequality `sum_divisor_mul_log_le` (from Jensen's formula) at each $t$,
  integrated over ..."; item 1: "so the same disk inequality for $f_X$ counts them".
