# The density layer on the zeta23 tree (QRH zeta23 add-on v2, step B3)

**Result: MNF_DENSITY=ACCEPTED**

zeta23 receipt (`RECEIPT-zeta23.md`): **PASS**. The run below is a second, separate Comparator run on the same tree: its challenge (`MNFChallengesD/*.lean`, every proof `sorry`, Mathlib only) states the theorems of the density layer and the definitions they use; its solution (`MNF.RH.DensityAll`) proves them, delegating to zeta23's theorems where it restates them. Comparator built both in its sandbox, exported both, and checked that every theorem statement and every definition (name, type and body) agrees and that the proofs use no axiom beyond propext, Quot.sound, Classical.choice; Lean's kernel and NanoDa replayed the solution.

- Comparator job `zeta23-density`: exit 0, started 2026-11-03T21:05:57Z, ended 2026-11-03T21:13:50Z (warm with respect to the Zeta23 library, which the accepted zeta23-main run compiled; compiled earlier in this tree (step B2): warm for Core, Gap, Hypotheses, Counting, Zeta23Restated; cold for every module this add-on introduces)
- launch: systemd-user RestrictAddressFamilies=~AF_UNIX SystemCallArchitectures=native OOMPolicy=continue LimitSTACK=1G; AF_UNIX sockets in the job: denied
- 124 theorems named in the challenge config; 66 definitions in the challenge, all compared by name, type and body (definition_names is empty)
- tree: the zeta23 checkout at `/home/qrh/qrh-zeta23-work/formal-math/zeta23` as checked by zeta23-main, plus the layer's files under `MNF/`, `Zeta23/` and `MNFChallengesD/`, `MNF_AuditDensity.lean`, and `lean_lib` stanzas appended to `lakefile.toml`
- layer files (sha256 listing): `9345643db224c306fd12fdc7bc08aababe56fd208e881635d492f6dad78ede7b`; lakefile.toml after the append: `51b09c56356db2ea0d62034a534601e551d07f32f6db18efde66d77d629e18a9`
- sorries outside the claim set: Zeta23/BohrLandau.lean: meanSquare_strip, rightHalfBound_of_meanSquare (not in the claim set)

## What was proved

As printed by Lean (`#check`), from the audit compile:

```lean
MNF.RH.N0_le_Ncount : ∀ (T₁ T₂ : ℝ), MNF.RH.N0 T₁ T₂ ≤ MNF.RH.Ncount T₁ T₂
MNF.RH.NOff_le_Ncount : ∀ (δ T₁ T₂ : ℝ), MNF.RH.NOff δ T₁ T₂ ≤ MNF.RH.Ncount T₁ T₂
MNF.RH.on_line_density_one_of_gap : MNF.RH.BohrLandau →
  MNF.RH.NcountSuperlinear →
    ∀ {Δ : ℝ},
      0 < Δ → MNF.RH.SpectralGapHyp Δ → ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (1 - ε) * ↑(MNF.RH.Ncount 0 T) ≤ ↑(MNF.RH.N0 0 T)
MNF.RH.Ncount_eq_near_add_off : ∀ (δ T₁ T₂ : ℝ), MNF.RH.Ncount T₁ T₂ = MNF.RH.NNear δ T₁ T₂ + MNF.RH.NOff δ T₁ T₂
MNF.RH.ncountSuperlinear : MNF.RH.NcountSuperlinear
MNF.RH.offLine_le_one_third : ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, ↑(MNF.RH.NOffLine 0 T) ≤ (1 / 3 + ε) * ↑(MNF.RH.Ncount 0 T)
MNF.RH.reservoirDensityOne_of_bohrLandau : MNF.RH.BohrLandau → MNF.RH.ReservoirDensityOne
MNF.RH.near_line_density_one : MNF.RH.ReservoirDensityOne →
  ∀ {δ : ℝ}, 0 < δ → ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (1 - ε) * ↑(MNF.RH.Ncount 0 T) ≤ ↑(MNF.RH.NNear δ 0 T)
MNF.RH.nullified_density_one : MNF.RH.ReservoirDensityOne →
  ∀ {Δ : ℝ},
    0 < Δ →
      ∀ ε > 0,
        ∃ T₀,
          ∀ T ≥ T₀,
            (1 - ε) * ↑(MNF.RH.Ncount 0 T) ≤
              ↑(∑ᶠ (ρ : ℂ) (_ : ρ ∈ MNF.RH.zerosIn 0 T ∩ {ρ | MNF.RH.nullify Δ (ρ.re - 1 / 2) = 0}),
                  MNF.RH.zeta_order ρ)
MNF.RH.onLineDensityOne_of_reservoir_of_gap : MNF.RH.ReservoirDensityOne →
  ∀ {Δ : ℝ}, 0 < Δ → MNF.RH.SpectralGapHyp Δ → MNF.RH.OnLineDensityOne
MNF.RH.onLineDensityOne_of_gap : MNF.RH.BohrLandau →
  ∀ {Δ : ℝ}, 0 < Δ → MNF.RH.SpectralGapHyp Δ → MNF.RH.OnLineDensityOne
MNF.RH.NLeft_eq_NRight : ∀ (δ T : ℝ), MNF.RH.NLeft δ T = MNF.RH.NRight δ T
MNF.RH.bohrLandau_of_right : MNF.RH.RightHalfBound → MNF.RH.BohrLandau
MNF.RH.onLineDensityOne_of_right : MNF.RH.RightHalfBound →
  ∀ {Δ : ℝ}, 0 < Δ → MNF.RH.SpectralGapHyp Δ → MNF.RH.OnLineDensityOne
MNF.RH.reservoirDensityOne_of_right : MNF.RH.RightHalfBound → MNF.RH.ReservoirDensityOne
MNF.Extension.conservation : ∀ (Δ x : ℝ), MNF.Extension.nullify Δ x + MNF.Extension.remainder Δ x = x
MNF.Extension.idempotent' : ∀ (Δ x : ℝ), MNF.Extension.nullify Δ (MNF.Extension.nullify Δ x) = MNF.Extension.nullify Δ x
MNF.Extension.dilation_covariance : ∀ (Δ x c : ℝ),
  0 < c → MNF.Extension.nullify (c * Δ) (c * x) = c * MNF.Extension.nullify Δ x
MNF.Extension.abs_nullify_antitone_in_threshold : ∀ (Δ₁ Δ₂ x : ℝ),
  Δ₁ ≤ Δ₂ → |MNF.Extension.nullify Δ₂ x| ≤ |MNF.Extension.nullify Δ₁ x|
MNF.Extension.eject_gapped : ∀ (Δ : ℝ), 0 < Δ → ∀ (x : ℝ), MNF.Extension.Gapped Δ (MNF.Extension.eject Δ x)
MNF.Extension.eject_idem : ∀ (Δ : ℝ),
  0 < Δ → ∀ (x : ℝ), MNF.Extension.eject Δ (MNF.Extension.eject Δ x) = MNF.Extension.eject Δ x
MNF.Extension.nullify_eject : ∀ (Δ : ℝ),
  0 < Δ → ∀ (x : ℝ), MNF.Extension.nullify Δ (MNF.Extension.eject Δ x) = MNF.Extension.eject Δ x
MNF.Extension.eject_nullify : ∀ (Δ : ℝ),
  0 < Δ → ∀ (x : ℝ), MNF.Extension.eject Δ (MNF.Extension.nullify Δ x) = MNF.Extension.nullify Δ x
MNF.Extension.remainder_eject : ∀ (Δ : ℝ), 0 < Δ → ∀ (x : ℝ), MNF.Extension.remainder Δ (MNF.Extension.eject Δ x) = 0
MNF.Extension.eject_sub_nullify : ∀ (Δ : ℝ),
  0 < Δ →
    ∀ (x : ℝ),
      MNF.Extension.eject Δ x - MNF.Extension.nullify Δ x =
        if MNF.Extension.IsReservoir Δ x then if 0 < x then Δ else -Δ else 0
MNF.Extension.eject_probe_reading : ∀ (Δ x : ℝ),
  0 < x →
    x < Δ →
      MNF.Extension.IsEjectionThreshold Δ (MNF.Extension.eject Δ x) ∧
        MNF.Extension.NorthProbe Δ (MNF.Extension.eject Δ x) = Δ / 2
MNF.Extension.eject_dilation : ∀ (Δ x c : ℝ), 0 < c → MNF.Extension.eject (c * Δ) (c * x) = c * MNF.Extension.eject Δ x
MNF.Extension.nullify_comp_nullify : ∀ (a b x : ℝ),
  MNF.Extension.nullify a (MNF.Extension.nullify b x) = MNF.Extension.nullify (max a b) x
MNF.Extension.eject_comp_eject : ∀ (a b x : ℝ),
  0 < a → 0 < b → MNF.Extension.eject a (MNF.Extension.eject b x) = MNF.Extension.eject (max a b) x
MNF.Extension.nullify_floor : ∀ (Δ : ℝ),
  0 < Δ → ∀ (g x : ℝ), MNF.Extension.Gapped Δ g → 0 ≤ g → 0 ≤ x → (g ≤ x ↔ g ≤ MNF.Extension.nullify Δ x)
MNF.Extension.eject_ceiling : ∀ (Δ : ℝ),
  0 < Δ → ∀ (g x : ℝ), MNF.Extension.Gapped Δ g → 0 ≤ g → 0 ≤ x → (x ≤ g ↔ MNF.Extension.eject Δ x ≤ g)
MNF.Extension.deficit_deficit : ∀ (Δ : ℝ),
  0 < Δ → ∀ (x : ℝ), MNF.Extension.deficit Δ (MNF.Extension.deficit Δ x) = MNF.Extension.remainder Δ x
MNF.Extension.deficit_tripotent : ∀ (Δ : ℝ),
  0 < Δ →
    ∀ (x : ℝ), MNF.Extension.deficit Δ (MNF.Extension.deficit Δ (MNF.Extension.deficit Δ x)) = MNF.Extension.deficit Δ x
MNF.Extension.nullify_deficit : ∀ (Δ : ℝ), 0 < Δ → ∀ (x : ℝ), MNF.Extension.nullify Δ (MNF.Extension.deficit Δ x) = 0
MNF.Extension.northProbe_deficit : ∀ (Δ x : ℝ),
  0 < x → x < Δ → MNF.Extension.NorthProbe Δ (MNF.Extension.deficit Δ x) = MNF.Extension.SouthProbe Δ x
MNF.Extension.eject_eq_id_add_deficit : ∀ (Δ x : ℝ), MNF.Extension.eject Δ x = x + MNF.Extension.deficit Δ x
MNF.Extension.nullify_eq_id_sub_deficit_sq : ∀ (Δ : ℝ),
  0 < Δ → ∀ (x : ℝ), MNF.Extension.nullify Δ x = x - MNF.Extension.deficit Δ (MNF.Extension.deficit Δ x)
MNF.Extension.metricProj_branch : ∀ (Δ : ℝ),
  0 < Δ →
    ∀ (x : ℝ),
      MNF.Extension.IsReservoir Δ x →
        MNF.Extension.metricProj Δ x =
          if MNF.Extension.NorthProbe Δ |x| < 0 then MNF.Extension.nullify Δ x else MNF.Extension.eject Δ x
MNF.Extension.metricProj_deficit_swap : ∀ (Δ : ℝ),
  0 < Δ →
    ∀ (x : ℝ),
      0 < x →
        x < Δ →
          x ≠ Δ / 2 →
            MNF.Extension.metricProj Δ x + MNF.Extension.metricProj Δ (MNF.Extension.deficit Δ x) =
              MNF.Extension.nullify Δ x + MNF.Extension.eject Δ x
MNF.Extension.rep_conservation : ∀ (Δ : ℝ) (ρ : MNF.Extension.Rep),
  MNF.Extension.nu Δ ρ + MNF.Extension.hidden Δ ρ = MNF.Extension.content ρ
MNF.Extension.rep_not_distributive : ∀ (Δ : ℝ),
  0 < Δ → ∃ ρ, MNF.Extension.nu Δ ρ ≠ MNF.Extension.nullify Δ (MNF.Extension.content ρ)
MNF.Extension.content_inject : ∀ (x : ℝ) (k : ℕ), 0 < k → MNF.Extension.content (MNF.Extension.inject x k) = x
MNF.Extension.nu_inject : ∀ (Δ x : ℝ) (k : ℕ),
  0 < k → MNF.Extension.nu Δ (MNF.Extension.inject x k) = MNF.Extension.nullify (↑k * Δ) x
MNF.Extension.eps_inject : ∀ (Δ x : ℝ),
  0 < Δ → ∀ (k : ℕ), 0 < k → MNF.Extension.eps Δ (MNF.Extension.inject x k) = MNF.Extension.eject (↑k * Δ) x
MNF.Extension.inject_nullified : ∀ (Δ x : ℝ),
  0 < Δ → ∀ (k : ℕ), 0 < k → |x| < ↑k * Δ → MNF.Extension.nu Δ (MNF.Extension.inject x k) = 0
MNF.Extension.inject_at_kstar : ∀ (Δ x : ℝ),
  0 < Δ → MNF.Extension.nu Δ (MNF.Extension.inject x (MNF.Extension.kstar Δ x)) = 0
MNF.Extension.eventual_nullification : ∀ (Δ x : ℝ),
  0 < Δ → ∃ K, ∀ k ≥ K, MNF.Extension.nu Δ (MNF.Extension.inject x k) = 0
MNF.Extension.typeA_on_demand : ∀ (Δ x : ℝ),
  0 < Δ →
    Δ ≤ |x| →
      ∃ k,
        0 < k ∧
          (∀ p ∈ MNF.Extension.inject x k, MNF.Extension.nullify Δ p = 0) ∧
            MNF.Extension.nullify Δ (MNF.Extension.content (MNF.Extension.inject x k)) ≠ 0
MNF.Extension.compact_inject : ∀ (x : ℝ) (k : ℕ), 0 < k → MNF.Extension.compact (MNF.Extension.inject x k) = [x]
MNF.Extension.nullify_sees_through : ∀ (Δ x : ℝ) (k : ℕ),
  0 < k → MNF.Extension.nullify Δ (MNF.Extension.content (MNF.Extension.inject x k)) = MNF.Extension.nullify Δ x
MNF.Extension.refine_inject : ∀ (x : ℝ) (j k : ℕ),
  0 < j → 0 < k → MNF.Extension.refine (MNF.Extension.inject x j) k = MNF.Extension.inject x (j * k)
MNF.Extension.ladder_not_composite : ∀ (a b x : ℝ),
  b ≤ a → MNF.Extension.nullify a (MNF.Extension.nullify b x) = MNF.Extension.nullify a x
MNF.Extension.deltaStar_singleton : ∀ (x : ℝ), x ≠ 0 → MNF.Extension.deltaStar [x] = |x|
MNF.Extension.nu_eq_zero_of_all_below : ∀ (Δ : ℝ) (ρ : MNF.Extension.Rep), (∀ p ∈ ρ, |p| < Δ) → MNF.Extension.nu Δ ρ = 0
MNF.Extension.deltaStar_inject : ∀ (x : ℝ),
  x ≠ 0 → ∀ (k : ℕ), 0 < k → MNF.Extension.deltaStar (MNF.Extension.inject x k) = |x| / ↑k
MNF.Extension.sameSign_refine_le : ∀ (Δ : ℝ),
  0 < Δ →
    ∀ (ρ : MNF.Extension.Rep),
      MNF.Extension.SameSign ρ →
        ∀ (k : ℕ), 0 < k → |MNF.Extension.nu Δ (MNF.Extension.refine ρ k)| ≤ |MNF.Extension.nu Δ ρ|
MNF.Extension.sameSign_nu_le_content : ∀ (Δ : ℝ) (ρ : MNF.Extension.Rep),
  MNF.Extension.SameSign ρ → |MNF.Extension.nu Δ ρ| ≤ |MNF.Extension.content ρ|
MNF.Extension.sameSign_sign : ∀ (Δ : ℝ) (ρ : MNF.Extension.Rep),
  MNF.Extension.SameSign ρ → MNF.Extension.nu Δ ρ ≠ 0 → 0 < MNF.Extension.nu Δ ρ * MNF.Extension.content ρ
MNF.Extension.mixed_refine_can_increase : ∃ Δ ρ, |MNF.Extension.nu Δ (MNF.Extension.compact ρ)| < |MNF.Extension.nu Δ ρ|
MNF.Extension.zero_reading_uninformative : ∃ Δ ρ₁ ρ₂,
  MNF.Extension.nu Δ ρ₁ = 0 ∧
    MNF.Extension.nu Δ ρ₂ = 0 ∧
      MNF.Extension.content ρ₁ = 0 ∧ MNF.Extension.content ρ₂ ≠ 0 ∧ ∃ Δ' < Δ, MNF.Extension.nu Δ' ρ₂ ≠ 0
MNF.Extension.inProcess_ne_postHoc : ∀ (Δ : ℝ),
  0 < Δ → ∃ L v, MNF.Extension.inProcess Δ L 2 v = 0 ∧ MNF.Extension.postHoc Δ L 2 v ≠ 0
MNF.Extension.residue_eq : ∀ (Δ : ℝ) (ρ : MNF.Extension.Rep),
  MNF.Extension.residue Δ ρ = MNF.Extension.remainder Δ (MNF.Extension.content ρ) - MNF.Extension.hidden Δ ρ
MNF.Extension.two_piece_sign_safe : ∀ (Δ : ℝ),
  0 < Δ → ∀ (p q : ℝ), MNF.Extension.nu Δ [p, q] ≠ 0 → 0 < MNF.Extension.nu Δ [p, q] * (p + q)
MNF.Extension.residue_both_signs : ∀ (Δ : ℝ),
  0 < Δ →
    ∀ (x : ℝ),
      0 < x →
        x < Δ →
          ∃ ρp ρm,
            MNF.Extension.content ρp = x ∧
              MNF.Extension.content ρm = x ∧ MNF.Extension.nu Δ ρp = Δ ∧ MNF.Extension.nu Δ ρm = -Δ
MNF.Extension.realise : ∀ (Δ : ℝ),
  0 < Δ → ∀ (x r : ℝ), Δ ≤ |r| → ∃ ρ, MNF.Extension.content ρ = x ∧ MNF.Extension.nu Δ ρ = r
MNF.Extension.gate_minimax : ∀ (Δ : ℝ),
  0 < Δ →
    ∀ (F : List ℝ → ℤ) (M : List ℝ),
      (∀ r ∈ M, Δ ≤ |r|) →
        F M ≠ 0 →
          ∃ x,
            x ≠ 0 ∧
              (∃ ρs, List.map (MNF.Extension.nu Δ) ρs = M ∧ ∀ ρ ∈ ρs, MNF.Extension.content ρ = x) ∧ ↑(F M) * x < 0
MNF.Extension.soft_idem_iff : ∀ (Δ p w : ℝ),
  (∀ (x : ℝ), MNF.Extension.softNullify Δ p (MNF.Extension.softNullify Δ p x w) w = MNF.Extension.softNullify Δ p x w) ↔
    MNF.Extension.softGate Δ p w = 0 ∨ MNF.Extension.softGate Δ p w = 1
MNF.Extension.soft_no_gap : ∀ (g Δ' : ℝ), 0 < g → g < 1 → 0 < Δ' → ∃ x, 0 < |x * g| ∧ |x * g| < Δ'
MNF.Extension.hardGate_is_nullify : ∀ (Δ x : ℝ), (x * if Δ ≤ |x| then 1 else 0) = MNF.Extension.nullify Δ x
MNF.Extension.injectAdd_ejectAdd : ∀ (Δ x y : ℝ), MNF.Extension.injectAdd Δ x y + MNF.Extension.ejectAdd Δ x y = x + y
MNF.Extension.ejectAdd_not_additive : ∀ (Δ : ℝ),
  0 < Δ → ∃ x y, MNF.Extension.ejectAdd Δ x y ≠ MNF.Extension.nullify Δ x + MNF.Extension.nullify Δ y
MNF.RH.nullify_eq_extension : ∀ (Δ x : ℝ), MNF.RH.nullify Δ x = MNF.Extension.nullify Δ x
MNF.RH.eq_zero_iff_gapped_all : ∀ (x : ℝ), x = 0 ↔ ∀ Δ > 0, MNF.Extension.Gapped Δ x
MNF.RH.eq_zero_iff_eject_fixed_all : ∀ (x : ℝ), x = 0 ↔ ∀ Δ > 0, MNF.Extension.eject Δ x = x
MNF.RH.eq_zero_iff_nullified_all : ∀ (x : ℝ), x = 0 ↔ ∀ Δ > 0, MNF.RH.nullify Δ x = 0
MNF.RH.displacement_injectable : ∀ (Δ x : ℝ),
  0 < Δ →
    ∃ k,
      0 < k ∧ MNF.Extension.content (MNF.Extension.inject x k) = x ∧ MNF.Extension.nu Δ (MNF.Extension.inject x k) = 0
MNF.RH.trace_singleton : ∀ (x : ℝ), x ≠ 0 → MNF.Extension.deltaStar [x] = |x|
MNF.RH.trace_zero : MNF.Extension.deltaStar [0] = 0
MNF.RH.on_line_iff_eject_fixed_all : ∀ (ρ : ℂ),
  ρ.re = 1 / 2 ↔ ∀ Δ > 0, MNF.Extension.eject Δ (ρ.re - 1 / 2) = ρ.re - 1 / 2
MNF.RH.on_line_iff_nullified_all : ∀ (ρ : ℂ), ρ.re = 1 / 2 ↔ ∀ Δ > 0, MNF.RH.nullify Δ (ρ.re - 1 / 2) = 0
MNF.RH.on_line_iff_trace_zero : ∀ (ρ : ℂ), ρ.re = 1 / 2 ↔ MNF.Extension.deltaStar [ρ.re - 1 / 2] = 0
DPMV.cpow_neg_mul_I_eq_exp : ∀ (n : ℕ),
  0 < n → ∀ (t : ℝ), ↑n ^ (-↑t * Complex.I) = Complex.exp (-↑(Real.log ↑n) * Complex.I * ↑t)
DPMV.conj_cpow_neg_mul_I : ∀ (n : ℕ),
  0 < n → ∀ (t : ℝ), (starRingEnd ℂ) (↑n ^ (-↑t * Complex.I)) = Complex.exp (↑(Real.log ↑n) * Complex.I * ↑t)
DPMV.prod_eq_exp : ∀ (m n : ℕ),
  0 < m →
    0 < n →
      ∀ (t : ℝ),
        ↑m ^ (-↑t * Complex.I) * (starRingEnd ℂ) (↑n ^ (-↑t * Complex.I)) =
          Complex.exp (↑(Real.log ↑n - Real.log ↑m) * Complex.I * ↑t)
DPMV.integral_exp_I_mul : ∀ (c : ℝ),
  c ≠ 0 →
    ∀ (T : ℝ),
      ∫ (t : ℝ) in 0..T, Complex.exp (↑c * Complex.I * ↑t) = (Complex.exp (↑c * Complex.I * ↑T) - 1) / (↑c * Complex.I)
DPMV.integral_exp_I_mul_zero : ∀ (T : ℝ), ∫ (t : ℝ) in 0..T, Complex.exp (↑0 * Complex.I * ↑t) = ↑T
DPMV.norm_exp_I_mul_eq_one : ∀ (c T : ℝ), ‖Complex.exp (↑c * Complex.I * ↑T)‖ = 1
DPMV.norm_integral_exp_I_mul_le : ∀ (c : ℝ),
  c ≠ 0 → ∀ (T : ℝ), ‖∫ (t : ℝ) in 0..T, Complex.exp (↑c * Complex.I * ↑t)‖ ≤ 2 / |c|
DPMV.J_self : ∀ (T : ℝ) (n : ℕ), DPMV.J T n n = ↑T
DPMV.norm_J_le : ∀ (T : ℝ) (m n : ℕ), 0 < m → 0 < n → m ≠ n → ‖DPMV.J T m n‖ ≤ 2 / |Real.log (↑n / ↑m)|
DPMV.normSq_sum_expand : ∀ (a : ℕ → ℂ) (N : ℕ) (t : ℝ),
  ↑(‖∑ n ∈ Finset.Icc 1 N, a n * ↑n ^ (-↑t * Complex.I)‖ ^ 2) =
    ∑ m ∈ Finset.Icc 1 N,
      ∑ n ∈ Finset.Icc 1 N, a m * (starRingEnd ℂ) (a n) * Complex.exp (↑(Real.log ↑n - Real.log ↑m) * Complex.I * ↑t)
DPMV.integral_normSq_sum : ∀ (a : ℕ → ℂ) (N : ℕ) (T : ℝ),
  ↑(∫ (t : ℝ) in 0..T, ‖∑ n ∈ Finset.Icc 1 N, a n * ↑n ^ (-↑t * Complex.I)‖ ^ 2) =
    ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, a m * (starRingEnd ℂ) (a n) * DPMV.J T m n
DPMV.dirichlet_mean_value : ∀ (a : ℕ → ℂ) (N : ℕ) (T : ℝ),
  0 < T →
    ∫ (t : ℝ) in 0..T, ‖∑ n ∈ Finset.Icc 1 N, a n * ↑n ^ (-↑t * Complex.I)‖ ^ 2 ≤
      T * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 +
        ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, if m = n then 0 else ‖a m‖ * ‖a n‖ * (2 / |Real.log (↑n / ↑m)|)
DPMV2.integral_exp_mul_I : ∀ (c : ℝ),
  c ≠ 0 →
    ∀ (T : ℝ),
      ∫ (t : ℝ) in 0..T, Complex.exp (↑c * ↑t * Complex.I) = (Complex.exp (↑c * ↑T * Complex.I) - 1) / (↑c * Complex.I)
DPMV2.integral_exp_zero_mul_I : ∀ (T : ℝ), ∫ (t : ℝ) in 0..T, Complex.exp (↑0 * ↑t * Complex.I) = ↑T
DPMV2.norm_integral_exp_mul_I_le : ∀ (c : ℝ),
  c ≠ 0 → ∀ (T : ℝ), ‖∫ (t : ℝ) in 0..T, Complex.exp (↑c * ↑t * Complex.I)‖ ≤ 2 / |c|
DPMV2.ofReal_norm_sq_dirichlet : ∀ (a : ℕ → ℂ) (N : ℕ) (t : ℝ),
  ↑(‖∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-↑t * Complex.I * ↑(Real.log ↑n))‖ ^ 2) =
    ∑ m ∈ Finset.Icc 1 N,
      ∑ n ∈ Finset.Icc 1 N, a m * (starRingEnd ℂ) (a n) * Complex.exp (↑(Real.log ↑n - Real.log ↑m) * ↑t * Complex.I)
DPMV2.ofReal_integral_norm_sq_dirichlet : ∀ (a : ℕ → ℂ) (N : ℕ) (T : ℝ),
  ↑(∫ (t : ℝ) in 0..T, ‖∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-↑t * Complex.I * ↑(Real.log ↑n))‖ ^ 2) =
    ∑ m ∈ Finset.Icc 1 N,
      ∑ n ∈ Finset.Icc 1 N,
        a m * (starRingEnd ℂ) (a n) * ∫ (t : ℝ) in 0..T, Complex.exp (↑(Real.log ↑n - Real.log ↑m) * ↑t * Complex.I)
DPMV2.norm_integral_freq_le : ∀ (T : ℝ),
  0 < T →
    ∀ {m n : ℕ},
      1 ≤ m →
        1 ≤ n →
          ‖∫ (t : ℝ) in 0..T, Complex.exp (↑(Real.log ↑n - Real.log ↑m) * ↑t * Complex.I)‖ ≤
            if m = n then T else 2 / |Real.log ↑n - Real.log ↑m|
DPMV2.sum_bound_split : ∀ (a : ℕ → ℂ) (N : ℕ) (T : ℝ),
  (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, ‖a m‖ * ‖a n‖ * if m = n then T else 2 / |Real.log ↑n - Real.log ↑m|) =
    T * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 +
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, if m = n then 0 else ‖a m‖ * ‖a n‖ * (2 / |Real.log ↑n - Real.log ↑m|)
DPMV2.dirichlet_mean_value : ∀ (a : ℕ → ℂ) (N : ℕ) (T : ℝ),
  0 < T →
    ∫ (t : ℝ) in 0..T, ‖∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-↑t * Complex.I * ↑(Real.log ↑n))‖ ^ 2 ≤
      T * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 +
        ∑ m ∈ Finset.Icc 1 N,
          ∑ n ∈ Finset.Icc 1 N, if m = n then 0 else ‖a m‖ * ‖a n‖ * (2 / |Real.log ↑n - Real.log ↑m|)
sum_divisor_mul_log_le : ∀ (c : ℂ) (r R : ℝ) (f : ℂ → ℂ),
  0 < r →
    r < R →
      AnalyticOnNhd ℂ f (Metric.closedBall c R) →
        f c ≠ 0 →
          (∑ᶠ (u : ℂ), ↑((MeromorphicOn.divisor f (Metric.closedBall c r)) u)) * Real.log (R / r) ≤
            Real.circleAverage (fun z => Real.log ‖f z‖) c R - Real.log ‖f c‖
circleAverage_log_norm_le_half_log_circleAverage_sq_of_ae : ∀ (c : ℂ) (R : ℝ),
  0 < R →
    ∀ (f : ℂ → ℂ),
      ContinuousOn f (Metric.sphere c R) →
        CircleIntegrable (fun z => Real.log ‖f z‖) c R →
          (∀ᵐ (θ : ℝ) ∂MeasureTheory.volume.restrict (Set.Ioc 0 (2 * Real.pi)), f (circleMap c R θ) ≠ 0) →
            Real.circleAverage (fun z => Real.log ‖f z‖) c R ≤
              1 / 2 * Real.log (Real.circleAverage (fun z => ‖f z‖ ^ 2) c R)
circleAverage_log_norm_le_half_log_circleAverage_sq : ∀ (c : ℂ) (R : ℝ),
  0 < R →
    ∀ (f : ℂ → ℂ),
      ContinuousOn f (Metric.sphere c R) →
        CircleIntegrable (fun z => Real.log ‖f z‖) c R →
          (∀ᵐ (θ : ℝ) ∂MeasureTheory.volume.restrict (Set.Ioc 0 (2 * Real.pi)), f (circleMap c R θ) ≠ 0) →
            0 < Real.circleAverage (fun z => ‖f z‖ ^ 2) c R →
              Real.circleAverage (fun z => Real.log ‖f z‖) c R ≤
                1 / 2 * Real.log (Real.circleAverage (fun z => ‖f z‖ ^ 2) c R)
AnalyticOnNhd.ae_circleMap_ne_zero : ∀ (c : ℂ) (R : ℝ),
  0 < R →
    ∀ (f : ℂ → ℂ),
      AnalyticOnNhd ℂ f (Metric.closedBall c R) →
        f c ≠ 0 → ∀ᵐ (θ : ℝ) ∂MeasureTheory.volume.restrict (Set.Ioc 0 (2 * Real.pi)), f (circleMap c R θ) ≠ 0
AnalyticOnNhd.circleAverage_log_norm_le_half_log_circleAverage_sq : ∀ (c : ℂ) (R : ℝ),
  0 < R →
    ∀ (f : ℂ → ℂ),
      AnalyticOnNhd ℂ f (Metric.closedBall c R) →
        f c ≠ 0 →
          Real.circleAverage (fun z => Real.log ‖f z‖) c R ≤
            1 / 2 * Real.log (Real.circleAverage (fun z => ‖f z‖ ^ 2) c R)
```

## How to read this

- `MNF/RH/GapDensity.lean` (add-on v3's file; docstrings revised): the window split under a gap and the conditional density-one theorem. `MNF/RH/Density.lean`: `NcountSuperlinear` is a theorem here (delegated to zeta23's Riemann–von Mangoldt formula); off-line zeros carry at most 1/3 + ε of N(0,T) (zeta23's Theorem B restated); `ReservoirDensityOne` (for every fixed δ, density one within δ of the line) follows from Bohr–Landau alone; `OnLineDensityOne` follows from Bohr–Landau together with a gap at some Δ > 0; Bohr–Landau is reduced, by the reflection ρ ↦ 1 − ρ̄, to its right-half form. Bohr–Landau itself is NOT proved: `Zeta23/BohrLandau.lean` names its two analytic inputs as `sorry` lemmas, which are not in the claim set and on which no claimed theorem depends.
- `MNF/RH/Strip.lean` and `MNF/Extension/InjectionEjection.lean`: the threshold, ejection and injection operators and the band around the line; bookkeeping with no analytic content. `Zeta23/BL/*.lean`: a Dirichlet-polynomial mean-value inequality (two forms) and Jensen-disc inequalities, Mathlib-only, the first lemmas toward Bohr–Landau.
- None of this proves, weakens or replaces `SpectralGapHyp` (RH for Δ ≥ 1/2; an open zero-free strip for 0 < Δ < 1/2); `OnLineDensityOne` follows from RH and is not known to imply it. Nothing here uses OpenAI's 7/8 theorem, and no sentence should put the two together as one result.

## Axiom reports

| theorem | axioms |
|---|---|
| `MNF.RH.N0_le_Ncount` | Classical.choice, Quot.sound, propext |
| `MNF.RH.NOff_le_Ncount` | Classical.choice, Quot.sound, propext |
| `MNF.RH.gap_forces_NOff_eq` | Classical.choice, Quot.sound, propext |
| `MNF.RH.on_line_density_one_of_gap` | Classical.choice, Quot.sound, propext |
| `MNF.RH.nullify_eq_zero_iff` | Classical.choice, Quot.sound, propext |
| `MNF.RH.NNear_eq_nullified_count` | Classical.choice, Quot.sound, propext |
| `MNF.RH.Ncount_eq_near_add_off` | Classical.choice, Quot.sound, propext |
| `MNF.RH.N0_le_NNear` | Classical.choice, Quot.sound, propext |
| `MNF.RH.NOff_le_NOffLine` | Classical.choice, Quot.sound, propext |
| `MNF.RH.NNear_eq_N0_of_gap` | Classical.choice, Quot.sound, propext |
| `MNF.RH.ncountSuperlinear` | Classical.choice, Quot.sound, propext |
| `MNF.RH.offLine_le_one_third` | Classical.choice, Quot.sound, propext |
| `MNF.RH.NOff_le_one_third` | Classical.choice, Quot.sound, propext |
| `MNF.RH.reservoirDensityOne_of_bohrLandau` | Classical.choice, Quot.sound, propext |
| `MNF.RH.near_line_density_one` | Classical.choice, Quot.sound, propext |
| `MNF.RH.nullified_density_one` | Classical.choice, Quot.sound, propext |
| `MNF.RH.onLineDensityOne_of_reservoir_of_gap` | Classical.choice, Quot.sound, propext |
| `MNF.RH.onLineDensityOne_of_gap` | Classical.choice, Quot.sound, propext |
| `MNF.RH.NOff_eq_right_add_left` | Classical.choice, Quot.sound, propext |
| `MNF.RH.NLeft_eq_NRight` | Classical.choice, Quot.sound, propext |
| `MNF.RH.bohrLandau_of_right` | Classical.choice, Quot.sound, propext |
| `MNF.RH.onLineDensityOne_of_right` | Classical.choice, Quot.sound, propext |
| `MNF.RH.reservoirDensityOne_of_right` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.conservation` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.idempotent'` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.dilation_covariance` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.abs_nullify_antitone_in_threshold` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.eject_gapped` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.eject_idem` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.nullify_eject` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.eject_nullify` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.remainder_eject` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.eject_sub_nullify` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.eject_probe_reading` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.eject_dilation` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.nullify_comp_nullify` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.eject_comp_eject` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.nullify_floor` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.eject_ceiling` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.deficit_deficit` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.deficit_tripotent` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.nullify_deficit` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.northProbe_deficit` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.eject_eq_id_add_deficit` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.nullify_eq_id_sub_deficit_sq` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.metricProj_branch` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.metricProj_deficit_swap` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.rep_conservation` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.rep_not_distributive` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.content_inject` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.nu_inject` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.eps_inject` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.inject_nullified` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.inject_at_kstar` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.eventual_nullification` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.typeA_on_demand` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.compact_inject` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.nullify_sees_through` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.refine_inject` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.ladder_not_composite` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.deltaStar_singleton` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.nu_eq_zero_of_all_below` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.deltaStar_inject` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.sameSign_refine_le` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.sameSign_nu_le_content` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.sameSign_sign` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.mixed_refine_can_increase` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.zero_reading_uninformative` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.inProcess_ne_postHoc` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.residue_eq` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.two_piece_sign_safe` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.residue_both_signs` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.realise` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.gate_minimax` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.soft_idem_iff` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.soft_no_gap` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.hardGate_is_nullify` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.injectAdd_ejectAdd` | Classical.choice, Quot.sound, propext |
| `MNF.Extension.ejectAdd_not_additive` | Classical.choice, Quot.sound, propext |
| `MNF.RH.nullify_eq_extension` | Classical.choice, Quot.sound, propext |
| `MNF.RH.mem_Band_iff_nullified` | Classical.choice, Quot.sound, propext |
| `MNF.RH.eject_fixed_iff_zero` | Classical.choice, Quot.sound, propext |
| `MNF.RH.eject_band_edge` | Classical.choice, Quot.sound, propext |
| `MNF.RH.eq_zero_iff_gapped_all` | Classical.choice, Quot.sound, propext |
| `MNF.RH.eq_zero_iff_eject_fixed_all` | Classical.choice, Quot.sound, propext |
| `MNF.RH.eq_zero_iff_nullified_all` | Classical.choice, Quot.sound, propext |
| `MNF.RH.displacement_injectable` | Classical.choice, Quot.sound, propext |
| `MNF.RH.injected_reads_zero_iff` | Classical.choice, Quot.sound, propext |
| `MNF.RH.band_injection_blind` | Classical.choice, Quot.sound, propext |
| `MNF.RH.trace_singleton` | Classical.choice, Quot.sound, propext |
| `MNF.RH.trace_zero` | Classical.choice, Quot.sound, propext |
| `MNF.RH.trace_inject_pos` | Classical.choice, Quot.sound, propext |
| `MNF.RH.trace_inject_tendsto` | Classical.choice, Quot.sound, propext |
| `MNF.RH.on_line_iff_eject_fixed_all` | Classical.choice, Quot.sound, propext |
| `MNF.RH.on_line_iff_nullified_all` | Classical.choice, Quot.sound, propext |
| `MNF.RH.on_line_iff_trace_zero` | Classical.choice, Quot.sound, propext |
| `MNF.RH.band_trivial_of_gap` | Classical.choice, Quot.sound, propext |
| `MNF.RH.gap_of_band_trivial` | Classical.choice, Quot.sound, propext |
| `DPMV.cpow_neg_mul_I_eq_exp` | Classical.choice, Quot.sound, propext |
| `DPMV.conj_cpow_neg_mul_I` | Classical.choice, Quot.sound, propext |
| `DPMV.prod_eq_exp` | Classical.choice, Quot.sound, propext |
| `DPMV.integral_exp_I_mul` | Classical.choice, Quot.sound, propext |
| `DPMV.integral_exp_I_mul_zero` | Classical.choice, Quot.sound, propext |
| `DPMV.norm_exp_I_mul_eq_one` | Classical.choice, Quot.sound, propext |
| `DPMV.norm_integral_exp_I_mul_le` | Classical.choice, Quot.sound, propext |
| `DPMV.J_self` | Classical.choice, Quot.sound, propext |
| `DPMV.norm_J_le` | Classical.choice, Quot.sound, propext |
| `DPMV.normSq_sum_expand` | Classical.choice, Quot.sound, propext |
| `DPMV.integral_normSq_sum` | Classical.choice, Quot.sound, propext |
| `DPMV.dirichlet_mean_value` | Classical.choice, Quot.sound, propext |
| `DPMV2.integral_exp_mul_I` | Classical.choice, Quot.sound, propext |
| `DPMV2.integral_exp_zero_mul_I` | Classical.choice, Quot.sound, propext |
| `DPMV2.norm_integral_exp_mul_I_le` | Classical.choice, Quot.sound, propext |
| `DPMV2.ofReal_norm_sq_dirichlet` | Classical.choice, Quot.sound, propext |
| `DPMV2.ofReal_integral_norm_sq_dirichlet` | Classical.choice, Quot.sound, propext |
| `DPMV2.log_sub_log_ne_zero` | Classical.choice, Quot.sound, propext |
| `DPMV2.norm_integral_freq_le` | Classical.choice, Quot.sound, propext |
| `DPMV2.sum_bound_split` | Classical.choice, Quot.sound, propext |
| `DPMV2.dirichlet_mean_value` | Classical.choice, Quot.sound, propext |
| `sum_divisor_mul_log_le` | Classical.choice, Quot.sound, propext |
| `circleAverage_log_norm_le_half_log_circleAverage_sq_of_ae` | Classical.choice, Quot.sound, propext |
| `circleAverage_log_norm_le_half_log_circleAverage_sq` | Classical.choice, Quot.sound, propext |
| `AnalyticOnNhd.ae_circleMap_ne_zero` | Classical.choice, Quot.sound, propext |
| `AnalyticOnNhd.circleAverage_log_norm_le_half_log_circleAverage_sq` | Classical.choice, Quot.sound, propext |

## Hashes

```
c768a8b2b1b8cfeea30f7e4f532e490030c611ff3017b23aea919c11a04c8f25  MNF/RH/Core.lean
9419bf81bfddaafe641f0587998d98aade8a663b64f65cdef3bb97466840d343  MNF/RH/Counting.lean
fc6690f89f8d63dead455b1e95b98d36de12c170342da678563cd60293ca8069  MNF/RH/DensityAll.lean
f7c3828d0ff1a2b7504d9ba295a30a2844b232c447d442b414b0f267cd3849b4  MNF/RH/Density.lean
9670bf8245245633d6d091028bcb7aa24e9f4572c833a8f5a7d42e1ca8dcd0c6  MNF/RH/GapDensity.lean
5a008cd5d18eaed26eea66e236cbe5f0f3c7d0bd64a1d449e3232edf78494a71  MNF/RH/Gap.lean
5b3c90e3b39a95fab27cd99b06fed06ea1a61de51cb7b1fa9c836e4d56ec2026  MNF/RH/Hypotheses.lean
b0b569048fca09ea8a5b2da4f2d97df80105f565d0342c23f41e1a135ecabbaa  MNF/RH/Strip.lean
441912f9657657606c323c609e533471526a95fe71a2372fbbc1ef586c9258aa  MNF/RH/Zeta23Restated.lean
25733057e1881d5807f707c99fe2bba58ef992b02861132bd92ce43a560c40cf  MNF/Extension/InjectionEjection.lean
fcab5f5a1ff4c6855f1d484137f4a33a09dd3e3c9a11a8642f08d864fce20f84  Zeta23/Superlinear.lean
66347d2bb643389ecee3e23d04119f1c5b45a09c806adde5398c3b81796ff51c  Zeta23/OffLine.lean
95f4cd15341fd31fa70c74ebfab2db68c9dba3e8047e041df865a0cfe5f2f00a  Zeta23/BohrLandau.lean
ae7e1ac9ba83a8c755b6a91d75ecbe8eb44d495bc1f8089080b24d23a9eefcf5  Zeta23/MNFBridge.lean
e3a250896756b8a5e0e40cb2c9913859974d032514149ae16f03d37396b14198  Zeta23/BL/DPMVexp.lean
ae6302bfc130f23f00f49c8dd0901a7a13ad1778ddcdc3f45b398a640522ca35  Zeta23/BL/DPMV.lean
87833f745a223e1c04fc488a142f3d93bf3144241fb1784df45323e4b228200f  Zeta23/BL/JensenDisc.lean
9f3a7f0b5f44ec30f04c43817d4996de6702912f94a6faaf0cc5da80e780ae02  MNFChallengesD/All.lean
3276cb7899cdae80c141ffd6b695e7a17a1776c529e5d70774e796afe83a0c29  MNFChallengesD/Core.lean
d4cca2d149bb6154ca2a0661bcddf8c803524c9db5f7182c310a2526dd74ac32  MNFChallengesD/Counting.lean
9ccd6e835e58e79663bb168ce4bf57e8c129d0b83dca47ee036016e33500cea8  MNFChallengesD/Density.lean
a12f3bc97cd8289c93ed8657ebd9428c611088e8ab04d4e59a05f8d584c17d35  MNFChallengesD/DPMVexp.lean
99884ae3e677e32d2a00abd3d57c0f33786caba72dbee30ab0c2ce6565cdebaf  MNFChallengesD/DPMV.lean
9081c4db7db74e839fd83d3cc1f568fd17732c777b4bc5cdf7cb69bd3815bf45  MNFChallengesD/Extension.lean
8ad3e0bc56fa9c98d19d296400c510f8c71c01c596f33996e3ac9d34773b6fe0  MNFChallengesD/GapDensity.lean
983a1e3f2dbf6c41463011243f28907eea763a604159885b89b3a88e6c07cd15  MNFChallengesD/Gap.lean
903b739ccb09eb1f1644f6423cc4196dbc7ae7a3a61dbb406ccda172cd2f9d62  MNFChallengesD/Hypotheses.lean
9ef5e092c2bbfb721f7eb4a2fb6cba83acff3c9aa1cb4140d6d531d610214f91  MNFChallengesD/JensenDisc.lean
191ebb118ab10e9b72dd09fed19d6d9d53d12f70607defecd4df267f0c7ecf08  MNFChallengesD/Strip.lean
d8845b766a908c914b8c1758074bbb6ed4c89767c456e0fc1ab642e8d39280e6  MNFChallengesD/Density.json
5319d99249b8af627ec1203266aefb93fa0c440f6d7727029daccd006fbf6953  MNF_AuditDensity.lean
51b09c56356db2ea0d62034a534601e551d07f32f6db18efde66d77d629e18a9  lakefile.toml
```

## Last lines of Comparator's log

```
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hg1
Note: This linter can be disabled with `set_option linter.unusedVariables false`
✔ [8845/8846] Built MNF.RH.Strip (4.3s)
✔ [8846/8846] Built MNF.RH.DensityAll (3.4s)
Build completed successfully (8846 jobs).
Exporting #[Nat, String, String.mk, Char, Quot, Quot.mk, Quot.lift, Quot.ind, MNF.RH.N0_le_Ncount, MNF.RH.NOff_le_Ncount, MNF.RH.gap_forces_NOff_eq, MNF.RH.on_line_density_one_of_gap, MNF.RH.nullify_e
Running nanoda kernel on solution
Nanoda kernel accepts the solution
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```
