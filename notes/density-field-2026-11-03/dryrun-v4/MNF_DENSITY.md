# The density layer on the zeta23 tree (QRH zeta23 add-on v4, step B3)

**Result: MNF_DENSITY=ACCEPTED**

zeta23 receipt (`RECEIPT-zeta23.md`): **PASS**. The run below is a second, separate Comparator run on the same tree: its challenge (`MNFChallengesD/*.lean`, every proof `sorry`, Mathlib only) states the theorems of the density layer and the definitions they use; its solution (`MNF.RH.DensityAll`) proves them, delegating to zeta23's theorems where it restates them. Comparator built both in its sandbox, exported both, and checked that every theorem statement and every definition (name, type and body) agrees and that the proofs use no axiom beyond propext, Quot.sound, Classical.choice; Lean's kernel and NanoDa replayed the solution.

- Comparator job `zeta23-density-v4`: exit 0, started 2026-11-03T23:51:54Z, ended 2026-11-03T23:58:23Z (warm with respect to the Zeta23 library, which the accepted zeta23-main run compiled; compiled earlier in this tree (step B2): warm for Core, Gap, Hypotheses, Counting, Zeta23Restated; compiled earlier in this tree (v2/v3 runs): MNF/RH/GapDensity MNF/RH/Density MNF/RH/Strip MNF/RH/DensityPartial MNF/Extension/InjectionEjection Zeta23/Superlinear Zeta23/OffLine Zeta23/BohrLandau Zeta23/BL/DPMV Zeta23/BL/DPMVexp Zeta23/BL/JensenDisc Zeta23/BL/BohrLandauPartial; cold for every module v4 introduces)
- launch: systemd-user RestrictAddressFamilies=~AF_UNIX SystemCallArchitectures=native OOMPolicy=continue LimitSTACK=1G; AF_UNIX sockets in the job: denied
- 334 theorems named in the challenge config; 81 definitions in the challenge, all compared by name, type and body (definition_names is empty)
- tree: the zeta23 checkout at `/home/joeyxyxyz/mnf-stageB/z23work/formal-math/zeta23` as checked by zeta23-main, plus the layer's files under `MNF/`, `Zeta23/` and `MNFChallengesD/`, `MNF_AuditDensity.lean`, and `lean_lib` stanzas appended to `lakefile.toml`
- layer files (sha256 listing): `c51dfb1c26a3223cc74ff0b2862cdf14957e859ef3704c8eb2c28b72def1982f`; lakefile.toml after the append: `139407bde7756f433f99500ba91ccb5ba7db053fb4655c2b10f711a683fdd8f9`
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
M1.mv_Icc : ∀ (N : ℕ) (x : ℕ → ℂ),
  ‖∑ m ∈ Finset.Icc 1 N,
        ∑ n ∈ Finset.Icc 1 N, if m = n then 0 else x m * (starRingEnd ℂ) (x n) / ↑(Real.log ↑m - Real.log ↑n)‖ ≤
    13 * ∑ n ∈ Finset.Icc 1 N, (↑n + 1) * ‖x n‖ ^ 2
M1.term_eq : ∀ (a : ℕ → ℂ) (T : ℝ) {m n : ℕ},
  1 ≤ m →
    1 ≤ n →
      a m * (starRingEnd ℂ) (a n) * DPMV.J T m n =
        ((if m = n then ↑T * (a m * (starRingEnd ℂ) (a m)) else 0) +
            Complex.I *
              if m = n then 0
              else
                a m * ↑m ^ (-↑T * Complex.I) * (starRingEnd ℂ) (a n * ↑n ^ (-↑T * Complex.I)) /
                  ↑(Real.log ↑m - Real.log ↑n)) -
          Complex.I * if m = n then 0 else a m * (starRingEnd ℂ) (a n) / ↑(Real.log ↑m - Real.log ↑n)
M1.Z_eq : ∀ (a : ℕ → ℂ) (N : ℕ) (T : ℝ),
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, a m * (starRingEnd ℂ) (a n) * DPMV.J T m n =
    (↑T * ∑ n ∈ Finset.Icc 1 N, a n * (starRingEnd ℂ) (a n) +
        Complex.I *
          ∑ m ∈ Finset.Icc 1 N,
            ∑ n ∈ Finset.Icc 1 N,
              if m = n then 0
              else
                a m * ↑m ^ (-↑T * Complex.I) * (starRingEnd ℂ) (a n * ↑n ^ (-↑T * Complex.I)) /
                  ↑(Real.log ↑m - Real.log ↑n)) -
      Complex.I *
        ∑ m ∈ Finset.Icc 1 N,
          ∑ n ∈ Finset.Icc 1 N, if m = n then 0 else a m * (starRingEnd ℂ) (a n) / ↑(Real.log ↑m - Real.log ↑n)
M1.norm_cpow_neg_mul_I : ∀ (n : ℕ), 0 < n → ∀ (T : ℝ), ‖↑n ^ (-↑T * Complex.I)‖ = 1
M1.dirichlet_meanSquare_le : ∀ (a : ℕ → ℂ) (N : ℕ) (T : ℝ),
  ∫ (t : ℝ) in 0..T, ‖∑ n ∈ Finset.Icc 1 N, a n * ↑n ^ (-↑t * Complex.I)‖ ^ 2 ≤
    T * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 + 26 * ∑ n ∈ Finset.Icc 1 N, (↑n + 1) * ‖a n‖ ^ 2
M1.cpow_neg_add_eq : ∀ (n : ℕ),
  0 < n → ∀ (σ t : ℝ), ↑n ^ (-(↑σ + ↑t * Complex.I)) = ↑(↑n ^ (-σ)) * ↑n ^ (-↑t * Complex.I)
M1.norm_sq_rpow : ∀ (n : ℕ) (σ : ℝ), ‖↑(↑n ^ (-σ))‖ ^ 2 = ↑n ^ (-2 * σ)
M1.sum_inv_le : ∀ (N : ℕ), ∑ n ∈ Finset.Icc 1 N, (↑n)⁻¹ ≤ 1 + Real.log ↑N
M1.sum_weight_le : ∀ σ ≤ 1,
  ∀ (N : ℕ), ∑ n ∈ Finset.Icc 1 N, (↑n + 1) * ↑n ^ (-2 * σ) ≤ 2 * ↑N ^ (2 - 2 * σ) * (Real.log ↑N + 1)
M1.meanValue_pow_raw : ∀ (σ : ℝ) (N : ℕ) (T : ℝ),
  ∫ (t : ℝ) in 0..T, ‖∑ n ∈ Finset.Icc 1 N, ↑n ^ (-(↑σ + ↑t * Complex.I))‖ ^ 2 ≤
    T * ∑ n ∈ Finset.Icc 1 N, ↑n ^ (-2 * σ) + 26 * ∑ n ∈ Finset.Icc 1 N, (↑n + 1) * ↑n ^ (-2 * σ)
M1.meanValue_pow : ∀ (σ : ℝ),
  1 / 2 < σ →
    σ ≤ 1 →
      ∀ (N : ℕ) (T : ℝ),
        0 < T →
          ∫ (t : ℝ) in 0..T, ‖∑ n ∈ Finset.Icc 1 N, ↑n ^ (-(↑σ + ↑t * Complex.I))‖ ^ 2 ≤
            T * ∑ n ∈ Finset.Icc 1 N, ↑n ^ (-2 * σ) + 52 * ↑N ^ (2 - 2 * σ) * (Real.log ↑N + 1)
M1.sum_rpow_neg_le : ∀ (σ : ℝ), 1 / 2 < σ → ∀ (N : ℕ), ∑ n ∈ Finset.Icc 1 N, ↑n ^ (-2 * σ) ≤ 1 + 1 / (2 * σ - 1)
M1.sum_weight_le_logfree : ∀ (σ : ℝ),
  1 / 2 < σ →
    σ < 1 → ∀ (N : ℕ), ∑ n ∈ Finset.Icc 1 N, (↑n + 1) * ↑n ^ (-2 * σ) ≤ 2 * (1 + ↑N ^ (2 - 2 * σ) / (2 - 2 * σ))
M1.meanValue_pow_logfree : ∀ (σ : ℝ),
  1 / 2 < σ →
    σ < 1 →
      ∀ (N : ℕ) (T : ℝ),
        ∫ (t : ℝ) in 0..T, ‖∑ n ∈ Finset.Icc 1 N, ↑n ^ (-(↑σ + ↑t * Complex.I))‖ ^ 2 ≤
          T * ∑ n ∈ Finset.Icc 1 N, ↑n ^ (-2 * σ) + 52 * (1 + ↑N ^ (2 - 2 * σ) / (2 - 2 * σ))
M1.meanValue_pow_explicit : ∀ (σ : ℝ),
  1 / 2 < σ →
    σ ≤ 1 →
      ∀ (N : ℕ) (T : ℝ),
        0 ≤ T →
          ∫ (t : ℝ) in 0..T, ‖∑ n ∈ Finset.Icc 1 N, ↑n ^ (-(↑σ + ↑t * Complex.I))‖ ^ 2 ≤
            T * (1 + 1 / (2 * σ - 1)) + 52 * ↑N ^ (2 - 2 * σ) * (Real.log ↑N + 1)
Zeta23.BL.M2.norm_add4_sq_le : ∀ (a b c d : ℂ), ‖a + b + c + d‖ ^ 2 ≤ 4 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2)
Zeta23.BL.M2.s_re : ∀ (σ t : ℝ), (↑σ + ↑t * Complex.I).re = σ
Zeta23.BL.M2.s_im : ∀ (σ t : ℝ), (↑σ + ↑t * Complex.I).im = t
Zeta23.BL.M2.one_sub_s_re : ∀ (σ t : ℝ), (1 - (↑σ + ↑t * Complex.I)).re = 1 - σ
Zeta23.BL.M2.one_sub_s_im : ∀ (σ t : ℝ), (1 - (↑σ + ↑t * Complex.I)).im = -t
Zeta23.BL.M2.neg_s_re : ∀ (σ t : ℝ), (-(↑σ + ↑t * Complex.I)).re = -σ
M3a.sum_Icc_one_eq : ∀ (f : ℕ → ℝ) {N : ℕ}, 1 ≤ N → ∑ n ∈ Finset.Icc 1 N, f n = f 1 + ∑ i ∈ Finset.Ico 1 N, f (i + 1)
Zeta23.BL.M3.continuous_Dpoly : ∀ (σ : ℝ) (N : ℕ), Continuous (Zeta23.BL.M3.Dpoly σ N)
Zeta23.BL.M3.meanValue_Dpoly : ∀ (σ : ℝ) (N : ℕ) (T : ℝ),
  ∫ (t : ℝ) in 0..T, ‖Zeta23.BL.M3.Dpoly σ N t‖ ^ 2 ≤
    T * ∑ n ∈ Finset.Icc 1 N, ↑n ^ (-2 * σ) + 26 * ∑ n ∈ Finset.Icc 1 N, (↑n + 1) * ↑n ^ (-2 * σ)
Zeta23.BL.M3.continuousOn_norm_zeta_sq : ∀ (σ T : ℝ),
  ContinuousOn (fun t => ‖riemannZeta (↑σ + ↑t * Complex.I)‖ ^ 2) (Set.Icc 1 T)
Zeta23.BL.neg_log_norm_riemannZeta_two_add_le : ∀ (t : ℝ), -Real.log ‖riemannZeta (2 + ↑t * Complex.I)‖ ≤ Real.log 3
Zeta23.BL.Lz_nonneg : ∀ (z : ℂ), 0 ≤ Zeta23.BL.Lz z
Zeta23.BL.log_norm_le_Lz : ∀ (z : ℂ), Real.log ‖riemannZeta z‖ ≤ Zeta23.BL.Lz z
Zeta23.BL.concaveOn_half_log_one_add : ConcaveOn ℝ (Set.Ici 0) fun x => 1 / 2 * Real.log (1 + x)
Zeta23.BL.circleMap_two_add : ∀ (t R θ : ℝ),
  circleMap (2 + ↑t * Complex.I) R θ = ↑(2 + R * Real.cos θ) + ↑(t + R * Real.sin θ) * Complex.I
Zeta23.BL.Lz_le_half_sq : ∀ (z : ℂ), Zeta23.BL.Lz z ≤ 1 / 2 * ‖riemannZeta z‖ ^ 2
Zeta23.BL.rightHalf_gt_sixth : ∀ (δ : ℝ), 1 / 6 < δ → ∃ C, ∀ (T : ℝ), 2 ≤ T → ↑(Zeta23.BL.NRight δ T) ≤ C * T
Zeta23.BL.bohrLandau_gt_sixth : ∀ (δ : ℝ), 1 / 6 < δ → ∃ C, ∀ (T : ℝ), 2 ≤ T → ↑(MNF.RH.NOff δ 0 T) ≤ C * T
Zeta23.BL.M45.zeta_one_lower : ∃ δ > 0, ∀ (t : ℝ), t ≠ 0 → |t| ≤ δ → |t|⁻¹ ≤ 4 * ‖riemannZeta (1 + ↑t * Complex.I)‖ ^ 2
Zeta23.BL.M45.meanSquare_one : ∃ C,
  ∀ (T : ℝ), 2 ≤ T → ∫ (t : ℝ) in 0..T, ‖riemannZeta (↑1 + ↑t * Complex.I)‖ ^ 2 ≤ C * T
Zeta23.BL.M45.meanSquare_one_from_one : ∃ C,
  ∀ (T : ℝ), 1 ≤ T → ∫ (t : ℝ) in 1..T, ‖riemannZeta (↑1 + ↑t * Complex.I)‖ ^ 2 ≤ C * T
MNF.RH.rightHalf_gt_sixth : ∀ (δ : ℝ), 1 / 6 < δ → ∃ C, ∀ (T : ℝ), 2 ≤ T → ↑(MNF.RH.NRight δ T) ≤ C * T
MNF.RH.bohrLandau_gt_sixth : ∀ (δ : ℝ), 1 / 6 < δ → ∃ C, ∀ (T : ℝ), 2 ≤ T → ↑(MNF.RH.NOff δ 0 T) ≤ C * T
BLClosure.cos_mode_fract : ∀ (ν : ℕ) (u : ℝ),
  Real.cos (2 * Real.pi * (↑ν + 1) * u) = Real.cos (2 * Real.pi * (↑ν + 1) * Int.fract u)
BLClosure.B2per_fourier : ∀ (u : ℝ),
  HasSum (fun ν => Real.cos (2 * Real.pi * (↑ν + 1) * u) / (Real.pi ^ 2 * (↑ν + 1) ^ 2)) (BLClosure.B2per u)
BLClosure.P_fourier : ∀ (u : ℝ),
  HasSum (fun ν => Real.cos (2 * Real.pi * (↑ν + 1) * u) / (2 * Real.pi ^ 2 * (↑ν + 1) ^ 2)) (BLClosure.P u + 1 / 12)
BLClosure.P_nonpos : ∀ (u : ℝ), BLClosure.P u ≤ 0
BLClosure.P_intCast : ∀ (n : ℤ), BLClosure.P ↑n = 0
BLClosure.P_eq : ∀ (u : ℝ), BLClosure.P u = (Int.fract u ^ 2 - Int.fract u) / 2
BLClosure.psi_abs_le : ∀ (u : ℝ), |BLClosure.psi u| ≤ 1 / 2
BLClosure.P_abs_le : ∀ (u : ℝ), |BLClosure.P u| ≤ 1 / 8
BLClosure.P_natCast : ∀ (n : ℕ), BLClosure.P ↑n = 0
BLClosure.continuous_P : Continuous BLClosure.P
BLClosure.measurable_psi : Measurable BLClosure.psi
BLClosure.mode_integrand_eq : ∀ (σ t : ℝ) (ν : ℕ) {u : ℝ},
  0 < u →
    Complex.exp (2 * ↑Real.pi * Complex.I * ↑ν * ↑u) * ↑u ^ (-↑σ - ↑t * Complex.I - 2) =
      ↑(u ^ (-σ - 2)) * Complex.exp (Complex.I * ↑(2 * Real.pi * ↑ν * u - t * Real.log u))
BLClosure.re_w : ∀ (σ t : ℝ), (-↑σ - ↑t * Complex.I - 2).re = -σ - 2
BLClosure.re_phase : ∀ (ν : ℕ), (2 * ↑Real.pi * Complex.I * ↑ν).re = 0
BLClosure.re_phase' : ∀ (ν : ℕ), (2 * ↑Real.pi * Complex.I * (↑ν + 1)).re = 0
BLClosure.cmode_hasSum : ∀ (u : ℝ), HasSum (fun ν => BLClosure.cmode ν u) (BLClosure.P u + 1 / 12)
BLClosure.continuous_cmode : ∀ (ν : ℕ), Continuous (BLClosure.cmode ν)
BLClosure.cmode_abs_le : ∀ (ν : ℕ) (u : ℝ), |BLClosure.cmode ν u| ≤ 1 / (2 * Real.pi ^ 2) * (1 / (↑ν + 1) ^ 2)
BLClosure.cmode_eq : ∀ (ν : ℕ) (u : ℝ),
  ↑(BLClosure.cmode ν u) =
    ↑(1 / (2 * Real.pi ^ 2 * (↑ν + 1) ^ 2) / 2) *
      (Complex.exp (2 * ↑Real.pi * Complex.I * (↑ν + 1) * ↑u) +
        Complex.exp (-(2 * ↑Real.pi * Complex.I * (↑ν + 1) * ↑u)))
BLClosure.S_eq_Dpoly : ∀ (σ : ℝ) (N : ℕ) (t : ℝ), BLClosure.S N (↑σ + ↑t * Complex.I) = Zeta23.BL.M3.Dpoly σ N t
BLClosure.rightHalfBound : Zeta23.BL.RightHalfBound
BLClosure.bohrLandau_all : MNF.RH.BohrLandau
Zeta23.BL.rightHalf_all : ∀ (δ : ℝ), 0 < δ → ∃ C, ∀ (T : ℝ), 2 ≤ T → ↑(Zeta23.BL.NRight δ T) ≤ C * T
Zeta23.BL.rightHalfBound : Zeta23.BL.RightHalfBound
Zeta23.BL.bohrLandau_full : MNF.RH.BohrLandau
Zeta23.BL.rightHalfBound_of_meanSquare' : Zeta23.BL.ZetaMeanSquare → Zeta23.BL.RightHalfBound
MNF.RH.reservoirDensityOne_unconditional : MNF.RH.ReservoirDensityOne
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
| `M1.log_nat_gap` | Classical.choice, Quot.sound, propext |
| `M1.mv_Icc` | Classical.choice, Quot.sound, propext |
| `M1.log_sub_log_ne_zero` | Classical.choice, Quot.sound, propext |
| `M1.term_eq` | Classical.choice, Quot.sound, propext |
| `M1.Z_eq` | Classical.choice, Quot.sound, propext |
| `M1.norm_cpow_neg_mul_I` | Classical.choice, Quot.sound, propext |
| `M1.dirichlet_meanSquare_le` | Classical.choice, Quot.sound, propext |
| `M1.cpow_neg_add_eq` | Classical.choice, Quot.sound, propext |
| `M1.norm_sq_rpow` | Classical.choice, Quot.sound, propext |
| `M1.sum_inv_le` | Classical.choice, Quot.sound, propext |
| `M1.sum_weight_le` | Classical.choice, Quot.sound, propext |
| `M1.meanValue_pow_raw` | Classical.choice, Quot.sound, propext |
| `M1.meanValue_pow` | Classical.choice, Quot.sound, propext |
| `M1.sum_Icc_rpow_le_integral` | Classical.choice, Quot.sound, propext |
| `M1.sum_rpow_neg_le` | Classical.choice, Quot.sound, propext |
| `M1.sum_Icc_rpow_le` | Classical.choice, Quot.sound, propext |
| `M1.sum_weight_le_logfree` | Classical.choice, Quot.sound, propext |
| `M1.meanValue_pow_logfree` | Classical.choice, Quot.sound, propext |
| `M1.meanValue_pow_explicit` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M2.norm_add4_sq_le` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M2.s_re` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M2.s_im` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M2.one_sub_s_re` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M2.one_sub_s_im` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M2.neg_s_re` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M2.s_ne_one` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M2.s_ne_zero` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M2.norm_s_le` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M2.norm_one_sub_s_ge` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M2.rpow_sq_eq` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M2.norm_P_le` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M2.norm_P_le'` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M2.norm_Q_le` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M2.norm_Q_le'` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M2.norm_R_le_core` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M2.norm_R_le` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M2.norm_R_le_uniform` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M2.norm_R_le'` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M2.zeta_eq_four_terms` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M2.zeta_sub_sum_le` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M2.norm_zeta_sq_le` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M2.norm_zeta_sq_le'` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M2.one_div_cpow_eq_rpow_mul` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M2.range_sum_eq_Icc` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M2.range_sum_eq_twist` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M2.integral_range_sq_eq_Icc` | Classical.choice, Quot.sound, propext |
| `M3a.sum_Icc_one_eq` | Classical.choice, Quot.sound, propext |
| `M3a.antitoneOn_rpow_Icc` | Classical.choice, Quot.sound, propext |
| `M3a.sum_Ico_rpow_succ_le_integral` | Classical.choice, Quot.sound, propext |
| `M3a.sum_Icc_rpow_le` | Classical.choice, Quot.sound, propext |
| `M3a.sum_Icc_rpow_le_mul` | Classical.choice, Quot.sound, propext |
| `M3a.sum_Icc_rpow_le_tsum` | Classical.choice, Quot.sound, propext |
| `M3a.sum_Icc_rpow_neg_le_tsum_one_div` | Classical.choice, Quot.sound, propext |
| `M3a.sum_Icc_rpow_mul_log_le` | Classical.choice, Quot.sound, propext |
| `M3a.sum_Icc_rpow_mul_log_le_of_sigma` | Classical.choice, Quot.sound, propext |
| `M3a.sum_Icc_rpow_le_of_sigma` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M3.continuous_Dpoly` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M3.meanValue_Dpoly` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M3.norm_zeta_sq_le_unif` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M3.continuousOn_norm_zeta_sq` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M3.integral_inv_sq_one` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M3.integral_bound_abstract` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M3.meanSquare_param` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M3.N_choice` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M3.rpow_neg_le_of_choice` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M3.rpow_pos_le_of_choice` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M3.meanSquareUnif_explicit` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M3.meanSquareUnif_naive` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M3.meanSquareUnif_task` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.NRight_eq_zero_of_half_le` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.MNF_zerosIn_union` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.NRight_add` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.NRight_sub_eq` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.NRight_mono` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.zeta_order_eq_zero_of_ne_zero` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.divisor_riemannZeta_eq_int` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.divisor_riemannZeta_eq` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.sum_zeta_order_le_finsum_divisor` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.finsum_divisor_riemannZeta_eq` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.finsum_divisor_riemannZeta_eq_zerosIn` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.mem_closedBall_iff_sq` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.abs_re_im_sub_le_of_mem_closedBall` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.bounds_of_mem_closedBall_two` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.one_notMem_closedBall_two` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.re_ge_of_mem_closedBall_Rout` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.outer_disc_facts` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.geom_facts` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.one_notMem_closedBall_two_add` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.one_notMem_sphere_two_add` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.neg_log_norm_riemannZeta_two_add_le` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.count_disc_le` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.finset_sum_zeta_order_le_finsum_divisor` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.count_finset_le` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.Lz_nonneg` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.log_le_half_log_one_add_sq` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.log_norm_le_Lz` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.continuousOn_Lz` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.circleIntegrable_Lz` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.circleAverage_log_norm_le_Lz` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.concaveOn_half_log_one_add` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.circleAverage_Lz_le` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.count_finset_le_log_meanSq` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.closedBall_Rout_subset` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.count_window_le` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.count_window_le_log_meanSq` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.circleAverage_log_le_Lz` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.circleMap_two_add` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.circleMap_two_add_ne_one` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.continuousOn_Lz_circleMap` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.integrableOn_Lz_circleMap_prod` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.integrable_Lz_circleMap_prod_restrict` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.intervalIntegrable_circleAverage_Lz` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.integral_circleAverage_Lz_eq_swap` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.Lz_le_half_sq` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.segment_mapsTo_ne_one` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.intervalIntegrable_Lz_segment` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.intervalIntegrable_normSq_zeta_segment` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.integral_Lz_circle_le` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.integral_circleAverage_Lz_le` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.count_le_integral` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.count_le_meanSquare` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.count_le_meanSquare'` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.tsum_one_div_rpow_anti` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.meanSquare_of_gt_one` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.meanSquare_hyp_extend` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.rightHalf_of_meanSquareUnif` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.rightHalf_gt_sixth` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.bohrLandau_gt_sixth` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M45.norm_zeta_le_strip` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M45.meanSquare_zero_one` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M45.continuous_norm_zeta_sq` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M45.zeta_one_lower` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M45.not_intervalIntegrable_zeta_one_sq` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M45.integral_zeta_one_sq_eq_zero` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M45.meanSquare_one` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M45.meanSquare_strip_lt_one` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M45.meanSquare_one_from_one` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M45.meanSquare_strip_of` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.M45.meanSquare_strip_from` | Classical.choice, Quot.sound, propext |
| `MNF.RH.rightHalf_gt_sixth` | Classical.choice, Quot.sound, propext |
| `MNF.RH.bohrLandau_gt_sixth` | Classical.choice, Quot.sound, propext |
| `MNF.RH.reservoirDensity_of_linear_bound` | Classical.choice, Quot.sound, propext |
| `MNF.RH.reservoirDensity_gt_sixth` | Classical.choice, Quot.sound, propext |
| `MNF.RH.near_line_density_gt_sixth` | Classical.choice, Quot.sound, propext |
| `MNF.RH.nullified_density_gt_sixth` | Classical.choice, Quot.sound, propext |
| `MNF.RH.onLineDensityOne_of_gap_gt_sixth` | Classical.choice, Quot.sound, propext |
| `BLClosure.hasSum_cos_div_sq_bernoulli` | Classical.choice, Quot.sound, propext |
| `BLClosure.cos_mode_fract` | Classical.choice, Quot.sound, propext |
| `BLClosure.B2per_fourier` | Classical.choice, Quot.sound, propext |
| `BLClosure.P_fourier` | Classical.choice, Quot.sound, propext |
| `BLClosure.P_nonpos` | Classical.choice, Quot.sound, propext |
| `BLClosure.P_intCast` | Classical.choice, Quot.sound, propext |
| `BLClosure.P_eq` | Classical.choice, Quot.sound, propext |
| `BLClosure.psi_abs_le` | Classical.choice, Quot.sound, propext |
| `BLClosure.P_abs_le` | Classical.choice, Quot.sound, propext |
| `BLClosure.P_natCast` | Classical.choice, Quot.sound, propext |
| `BLClosure.continuous_P` | Classical.choice, Quot.sound, propext |
| `BLClosure.measurable_psi` | Classical.choice, Quot.sound, propext |
| `BLClosure.hasDerivAt_P` | Classical.choice, Quot.sound, propext |
| `BLClosure.integrableOn_bdd_mul_cpow` | Classical.choice, Quot.sound, propext |
| `BLClosure.integrableOn_psi_mul` | Classical.choice, Quot.sound, propext |
| `BLClosure.integrableOn_P_mul` | Classical.choice, Quot.sound, propext |
| `BLClosure.tail_by_parts_interval` | Classical.choice, Quot.sound, propext |
| `BLClosure.tail_by_parts` | Classical.choice, Quot.sound, propext |
| `BLClosure.hasDerivAt_P'` | Classical.choice, Quot.sound, propext |
| `BLClosure.first_derivative_test_amp_smooth'` | Classical.choice, Quot.sound, propext |
| `BLClosure.first_derivative_test_amp_smooth` | Classical.choice, Quot.sound, propext |
| `BLClosure.first_derivative_test_smooth` | Classical.choice, Quot.sound, propext |
| `BLClosure.mode_integrand_eq` | Classical.choice, Quot.sound, propext |
| `BLClosure.mode_bound_interval` | Classical.choice, Quot.sound, propext |
| `BLClosure.integrableOn_bdd_mul_cpow'` | Classical.choice, Quot.sound, propext |
| `BLClosure.integrableOn_exp_mul_cpow` | Classical.choice, Quot.sound, propext |
| `BLClosure.integrableOn_exp_neg_mul_cpow` | Classical.choice, Quot.sound, propext |
| `BLClosure.re_w` | Classical.choice, Quot.sound, propext |
| `BLClosure.re_w_lt` | Classical.choice, Quot.sound, propext |
| `BLClosure.re_phase` | Classical.choice, Quot.sound, propext |
| `BLClosure.re_phase'` | Classical.choice, Quot.sound, propext |
| `BLClosure.tail_mode_bound'` | Classical.choice, Quot.sound, propext |
| `BLClosure.tail_mode_bound` | Classical.choice, Quot.sound, propext |
| `BLClosure.tail_mode_bound_neg` | Classical.choice, Quot.sound, propext |
| `BLClosure.cmode_hasSum` | Classical.choice, Quot.sound, propext |
| `BLClosure.continuous_cmode` | Classical.choice, Quot.sound, propext |
| `BLClosure.cmode_abs_le` | Classical.choice, Quot.sound, propext |
| `BLClosure.cmode_eq` | Classical.choice, Quot.sound, propext |
| `BLClosure.mode_integral_bound` | Classical.choice, Quot.sound, propext |
| `BLClosure.hasSum_mode_integrals` | Classical.choice, Quot.sound, propext |
| `BLClosure.split_P` | Classical.choice, Quot.sound, propext |
| `BLClosure.integral_cpow_tail` | Classical.choice, Quot.sound, propext |
| `BLClosure.tail_sharp` | Classical.choice, Quot.sound, propext |
| `BLClosure.zeta_eq_euler_maclaurin` | Classical.choice, Quot.sound, propext |
| `BLClosure.norm_natCast_cpow_neg_div_two` | Classical.choice, Quot.sound, propext |
| `BLClosure.zeta_approx_sharp` | Classical.choice, Quot.sound, propext |
| `BLClosure.zeta_approx_sharp_segment` | Classical.choice, Quot.sound, propext |
| `BLClosure.zeta_approx_sharp_segment'` | Classical.choice, Quot.sound, propext |
| `BLClosure.S_eq_Dpoly` | Classical.choice, Quot.sound, propext |
| `BLClosure.norm_main_term_le` | Classical.choice, Quot.sound, propext |
| `BLClosure.norm_zeta_sq_le_sharp` | Classical.choice, Quot.sound, propext |
| `BLClosure.meanSquare_sharp_param` | Classical.choice, Quot.sound, propext |
| `BLClosure.meanSquareUnif_all_of_lt_one` | Classical.choice, Quot.sound, propext |
| `BLClosure.meanSquareUnif_all` | Classical.choice, Quot.sound, propext |
| `BLClosure.meanSquareUnifFrom_all` | Classical.choice, Quot.sound, propext |
| `BLClosure.rightHalfBound` | Classical.choice, Quot.sound, propext |
| `BLClosure.bohrLandau_all` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.rightHalf_all` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.rightHalfBound` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.bohrLandau_full` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.rightHalfBound_of_meanSquare'` | Classical.choice, Quot.sound, propext |
| `Zeta23.BL.meanSquare_strip'` | Classical.choice, Quot.sound, propext |
| `MNF.RH.reservoirDensityOne_unconditional` | Classical.choice, Quot.sound, propext |
| `MNF.RH.onLineDensityOne_of_gap_only` | Classical.choice, Quot.sound, propext |

## Hashes

```
c768a8b2b1b8cfeea30f7e4f532e490030c611ff3017b23aea919c11a04c8f25  MNF/RH/Core.lean
9419bf81bfddaafe641f0587998d98aade8a663b64f65cdef3bb97466840d343  MNF/RH/Counting.lean
6d0cf03be97a7dec4b1f6bfb4b3f95c21a2b82a6e181fe690349e174476d66d6  MNF/RH/DensityAll.lean
f7c3828d0ff1a2b7504d9ba295a30a2844b232c447d442b414b0f267cd3849b4  MNF/RH/Density.lean
46c7ab109c4497f8494a188d501a48e429f624204aa0e56a9ef8564d245f3c08  MNF/RH/DensityPartial.lean
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
32e89e1a18949842089fd014c19338be1ec46a9412a015fbf2176877e7e08b82  Zeta23/BL/BohrLandauClosure.lean
04a4f8d46758d3fb466ca1668c203f4794cd3d440bba48ec656645505faa6e92  Zeta23/BL/BohrLandauPartial.lean
e3a250896756b8a5e0e40cb2c9913859974d032514149ae16f03d37396b14198  Zeta23/BL/DPMVexp.lean
ae6302bfc130f23f00f49c8dd0901a7a13ad1778ddcdc3f45b398a640522ca35  Zeta23/BL/DPMV.lean
87833f745a223e1c04fc488a142f3d93bf3144241fb1784df45323e4b228200f  Zeta23/BL/JensenDisc.lean
d92b36b2d9c210e9d40960b48ceb8dfdb4eafc3c3b5c19137af546222b5c9c8f  MNFChallengesD/All.lean
5d2d6288a6a23aa170c05b52c49b2cfdb8007cb4072517510d02e2a4afc58361  MNFChallengesD/BohrLandauClosure.lean
9e888ea96c38e5cb4870344495b231f44b169b20b97caf13a6be9d76ffc7107e  MNFChallengesD/BohrLandau.lean
020e6aef286cd10a14f5adb69b4fbb455088891eb0fa4f199da4fd8109368fdc  MNFChallengesD/BohrLandauPartial.lean
06664f4d96e7996a79194c83c4bdb7a9b7fa43becb45823f6a8d53525455d060  MNFChallengesD/Core.lean
451f6699b2922dc5d5456ae05bf7be5b4f56da0cc94a5ecd69776ea93913fa5b  MNFChallengesD/Counting.lean
694f6379b39f806a39bb4d911c982c26a038b5ccb5791d0ff598d216757f415d  MNFChallengesD/Density.lean
d8bdec5ebc98f4664da9673ceda1fc0ae59f4062117bcd43bbeb24875bd647e1  MNFChallengesD/DensityPartial.lean
6c664372b855ecd6733563d9d4d938309cee3c7a55d3b894b07057e137200ceb  MNFChallengesD/DPMVexp.lean
4708d1fc01e3a1262547db859aa55a93fb7bca19b3caf8d71662482f155f67db  MNFChallengesD/DPMV.lean
f2a3e6250788f7fcf44abeb1a8ff8caa83a30d7a549076ce134a16cca4da67f9  MNFChallengesD/Extension.lean
a74e951e45c012aad30fe4b6ae4763b3ead1b4ee1434e100cd781b60595b5f66  MNFChallengesD/GapDensity.lean
8e09ebfba5d04d6a0f61905262af05bd5cc1b13995e7d784e05b6472eefe5fd4  MNFChallengesD/Gap.lean
1c14951e98022623999f3886c1d0c612d166de26d47dfb682b86f1d3f30820ed  MNFChallengesD/Hypotheses.lean
074bea579a7702add0027b8d7a9e78819981c26fd640eb8689608a2c75af7686  MNFChallengesD/JensenDisc.lean
03a0fb60bea2d376c9f5372299abce8d36be8277d263417cc9b8822773b4ef0d  MNFChallengesD/Strip.lean
e6449764e10b8ca001bfb3c100928bdb4b5905f129379953ae97bc905112896e  MNFChallengesD/Density.json
276e862f2206fb08ddb9bb0a2893f973358c79a8d95863680a3e7d25b567ad15  MNF_AuditDensity.lean
139407bde7756f433f99500ba91ccb5ba7db053fb4655c2b10f711a683fdd8f9  lakefile.toml
```

## Last lines of Comparator's log

```
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hg1
Note: This linter can be disabled with `set_option linter.unusedVariables false`
✔ [8848/8849] Built Zeta23.BL.BohrLandauClosure (11s)
✔ [8849/8849] Built MNF.RH.DensityAll (3.5s)
Build completed successfully (8849 jobs).
Exporting #[Nat, String, String.mk, Char, Quot, Quot.mk, Quot.lift, Quot.ind, MNF.RH.N0_le_Ncount, MNF.RH.NOff_le_Ncount, MNF.RH.gap_forces_NOff_eq, MNF.RH.on_line_density_one_of_gap, MNF.RH.nullify_e
Running nanoda kernel on solution
Nanoda kernel accepts the solution
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```
