import Mathlib

open Filter MeromorphicAt MeasureTheory MeromorphicOn Metric Real Set Topology

/-- Jensen's disc inequality: the number of zeros of `f` in the closed ball of radius `r`
(counted with multiplicity), times `log (R / r)`, is bounded by the circle average of
`log ‖f‖` on the circle of radius `R` minus `log ‖f c‖`. -/
theorem sum_divisor_mul_log_le (c : ℂ) (r R : ℝ) (f : ℂ → ℂ) (hr : 0 < r) (hrR : r < R)
    (h₁f : AnalyticOnNhd ℂ f (Metric.closedBall c R)) (h₂f : f c ≠ 0) :
    (∑ᶠ u, (MeromorphicOn.divisor f (Metric.closedBall c r)) u : ℝ) * Real.log (R / r)
      ≤ circleAverage (fun z => Real.log ‖f z‖) c R - Real.log ‖f c‖ := by
  have hR : 0 < R := hr.trans hrR
  have hRabs : |R| = R := abs_of_pos hR
  have h₁f' : AnalyticOnNhd ℂ f (closedBall c |R|) := by rwa [hRabs]
  have jensen := h₁f'.circleAverage_log_norm hR.ne' h₂f
  rw [hRabs] at jensen
  rw [jensen, add_sub_cancel_right, finsum_mul]
  refine finsum_le_finsum' ?_ ?_ fun u ↦ ?_
  · exact (divisor f (closedBall c r)).finiteSupport (isCompact_closedBall ..) |>.subset
      fun _ _ ↦ (by simp_all)
  · exact (divisor f (closedBall c R)).finiteSupport (isCompact_closedBall ..) |>.subset
      fun _ _ ↦ (by simp_all)
  · by_cases h1 : u ∈ closedBall c R
    · by_cases h2 : u ∈ closedBall c r
      · by_cases! h3 : u = c
        · subst h3
          rw [(h₁f.mono (closedBall_subset_closedBall hrR.le)).divisor_apply h2,
            (h₁f u h1).analyticOrderAt_eq_zero.mpr h₂f]
          simp
        · have hdiv : divisor f (closedBall c r) u = divisor f (closedBall c R) u := by
            rw [(h₁f.mono (closedBall_subset_closedBall hrR.le)).divisor_apply h2,
              h₁f.divisor_apply h1]
          rw [hdiv]
          have h0 : (0 : ℤ) ≤ divisor f (closedBall c R) u := by
            simpa using h₁f.divisor_nonneg u
          have h0' : (0 : ℝ) ≤ (divisor f (closedBall c R) u : ℝ) := by exact_mod_cast h0
          refine mul_le_mul_of_nonneg_left ?_ h0'
          have hpos : 0 < ‖c - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h3.symm)
          have hcu : ‖c - u‖ ≤ r := by simpa [dist_eq_norm'] using h2
          apply log_le_log (div_pos hR hr)
          rw [div_le_iff₀ hr, mul_right_comm, le_mul_inv_iff₀ hpos]
          exact mul_le_mul_of_nonneg_left hcu hR.le
      · simp only [h2, not_false_eq_true, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem,
          Int.cast_zero, zero_mul]
        refine mul_nonneg (mod_cast h₁f.divisor_nonneg ..) ?_
        apply log_nonneg
        simp only [mem_closedBall, dist_eq_norm', not_le] at h1 h2
        have : ‖c - u‖ ≠ 0 := (hr.trans h2).ne'
        rw [← div_eq_mul_inv, le_div_iff₀ (hr.trans h2), one_mul]
        exact h1
    · have : u ∉ closedBall c r := by
        simp_all
        linarith
      simp [h1, this]

/-- Jensen's inequality for `log` on a circle: if `log ‖f‖` is circle integrable and `f` does
not vanish almost everywhere on the circle, then the circle average of `log ‖f‖` is bounded by
half the log of the circle average of `‖f‖ ^ 2`.

The extra hypotheses are necessary: with only `ContinuousOn f (sphere c R)`, `log ‖f‖` may fail
to be integrable (then `circleAverage` is `0` by convention and the inequality can fail), and if
`f` vanishes on a set of positive measure the convention `log 0 = 0` also breaks the inequality. -/
theorem circleAverage_log_norm_le_half_log_circleAverage_sq_of_ae (c : ℂ) (R : ℝ) (hR : 0 < R)
    (f : ℂ → ℂ) (hf : ContinuousOn f (Metric.sphere c R))
    (hint : CircleIntegrable (fun z => Real.log ‖f z‖) c R)
    (hae : ∀ᵐ θ ∂(volume.restrict (Set.Ioc 0 (2 * π))), f (circleMap c R θ) ≠ 0) :
    circleAverage (fun z => Real.log ‖f z‖) c R
      ≤ (1/2) * Real.log (circleAverage (fun z => ‖f z‖ ^ 2) c R) := by
  have hI : uIoc (0:ℝ) (2 * π) = Ioc 0 (2 * π) := uIoc_of_le (by positivity)
  have : IsFiniteMeasure (volume.restrict (uIoc (0:ℝ) (2 * π))) := by
    rw [hI]; infer_instance
  have : NeZero (volume (uIoc (0:ℝ) (2 * π))) := ⟨by simp⟩
  have hcont : Continuous (fun θ : ℝ ↦ ‖f (circleMap c R θ)‖) :=
    (hf.comp_continuous (continuous_circleMap c R) (fun θ ↦ circleMap_mem_sphere c hR.le θ)).norm
  have hlogAe : ∀ᵐ θ ∂(volume.restrict (uIoc (0:ℝ) (2 * π))),
      exp (log ‖f (circleMap c R θ)‖) = ‖f (circleMap c R θ)‖ := by
    rw [hI]
    filter_upwards [hae] with θ hθ
    exact exp_log (norm_pos_iff.mpr hθ)
  have hint' : Integrable (fun θ ↦ log ‖f (circleMap c R θ)‖)
      (volume.restrict (uIoc (0:ℝ) (2 * π))) := by
    rw [hI]; exact hint.1
  rw [circleAverage_eq_intervalAverage, circleAverage_eq_intervalAverage]
  have h1 : exp (⨍ θ in (0:ℝ)..(2 * π), log ‖f (circleMap c R θ)‖)
      ≤ ⨍ θ in (0:ℝ)..(2 * π), ‖f (circleMap c R θ)‖ := by
    calc exp (⨍ θ in (0:ℝ)..(2 * π), log ‖f (circleMap c R θ)‖)
        ≤ ⨍ θ in (0:ℝ)..(2 * π), exp (log ‖f (circleMap c R θ)‖) := by
          refine convexOn_exp.map_average_le continuousOn_exp isClosed_univ (by simp) hint' ?_
          exact (integrable_congr hlogAe).mpr hcont.integrableOn_uIoc
      _ = ⨍ θ in (0:ℝ)..(2 * π), ‖f (circleMap c R θ)‖ := average_congr hlogAe
  have h2 : (⨍ θ in (0:ℝ)..(2 * π), ‖f (circleMap c R θ)‖) ^ 2
      ≤ ⨍ θ in (0:ℝ)..(2 * π), ‖f (circleMap c R θ)‖ ^ 2 := by
    refine (convexOn_pow 2).map_average_le (continuousOn_pow 2) isClosed_Ici
      (by filter_upwards; simp) ?_ ?_
    · exact hcont.integrableOn_uIoc
    · exact ((continuous_pow 2).comp hcont).integrableOn_uIoc
  have hA : 0 < ⨍ θ in (0:ℝ)..(2 * π), ‖f (circleMap c R θ)‖ := (exp_pos _).trans_le h1
  have h3 := log_le_log (pow_pos hA 2) h2
  rw [log_pow] at h3
  push_cast at h3
  have h4 : (⨍ θ in (0:ℝ)..(2 * π), log ‖f (circleMap c R θ)‖)
      ≤ log (⨍ θ in (0:ℝ)..(2 * π), ‖f (circleMap c R θ)‖) := by
    rw [← log_exp (⨍ θ in (0:ℝ)..(2 * π), log ‖f (circleMap c R θ)‖)]
    exact log_le_log (exp_pos _) h1
  linarith

set_option linter.unusedVariables false in
/-- The statement in the form requested by the density plan (the hypothesis `hpos` is implied
by the others and is not used). -/
theorem circleAverage_log_norm_le_half_log_circleAverage_sq (c : ℂ) (R : ℝ) (hR : 0 < R)
    (f : ℂ → ℂ) (hf : ContinuousOn f (Metric.sphere c R))
    (hint : CircleIntegrable (fun z => Real.log ‖f z‖) c R)
    (hae : ∀ᵐ θ ∂(volume.restrict (Set.Ioc 0 (2 * π))), f (circleMap c R θ) ≠ 0)
    (hpos : 0 < circleAverage (fun z => ‖f z‖ ^ 2) c R) :
    circleAverage (fun z => Real.log ‖f z‖) c R
      ≤ (1/2) * Real.log (circleAverage (fun z => ‖f z‖ ^ 2) c R) :=
  circleAverage_log_norm_le_half_log_circleAverage_sq_of_ae c R hR f hf hint hae

/-- For `f` analytic on a neighbourhood of the closed ball with `f c ≠ 0`, the zeros of `f` on
the circle are finite, so `log ‖f‖` is circle integrable and `f ≠ 0` a.e. on the circle. -/
theorem AnalyticOnNhd.ae_circleMap_ne_zero (c : ℂ) (R : ℝ) (hR : 0 < R) (f : ℂ → ℂ)
    (h₁f : AnalyticOnNhd ℂ f (Metric.closedBall c R)) (h₂f : f c ≠ 0) :
    ∀ᵐ θ ∂(volume.restrict (Set.Ioc 0 (2 * π))), f (circleMap c R θ) ≠ 0 := by
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Set.Finite.measure_zero ?_ _
  simp only [compl_ofPred, Classical.not_imp, Decidable.not_not]
  -- the set of θ ∈ Ioc 0 2π with f (circleMap c R θ) = 0 is finite
  have hfin : ((divisor f (closedBall c R)).support).Finite :=
    (divisor f (closedBall c R)).finiteSupport (isCompact_closedBall c R)
  refine Finite.of_finite_image (f := circleMap c R) (hfin.subset ?_) ?_
  · rintro z ⟨θ, ⟨hθ, heval⟩, rfl⟩
    have hz : circleMap c R θ ∈ closedBall c R :=
      sphere_subset_closedBall (circleMap_mem_sphere c hR.le θ)
    have hc : c ∈ closedBall c R := mem_closedBall_self hR.le
    have hord_c : analyticOrderAt f c ≠ ⊤ := by
      rw [(h₁f c hc).analyticOrderAt_eq_zero.mpr h₂f]; exact WithTop.zero_ne_top
    have hord : analyticOrderAt f (circleMap c R θ) ≠ ⊤ :=
      analyticOrderAt_ne_top_of_isPreconnected h₁f (convex_closedBall c R).isPreconnected hc hz
        hord_c
    have hord0 : analyticOrderAt f (circleMap c R θ) ≠ 0 := by
      rw [ne_eq, analyticOrderAt_eq_zero]
      push Not
      exact ⟨h₁f _ hz, heval⟩
    rw [Function.mem_support, h₁f.divisor_apply hz]
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hord
    rw [← hn] at hord0 ⊢
    intro h
    apply hord0
    have hn0 : n = 0 := by simpa [ENat.map_natCast] using h
    simp [hn0]
  · grw [ofPred_and, inter_subset_left]
    have hinj : (uIoc (0:ℝ) (2 * π)).InjOn (circleMap c R) :=
      injOn_circleMap_of_abs_sub_le (a := 0) (b := 2 * π) hR.ne' (by simp [abs_of_pos pi_pos])
    rw [uIoc_of_le (by positivity : (0:ℝ) ≤ 2 * π)] at hinj
    exact hinj

/-- Jensen's inequality for `log` on a circle, for `f` analytic on a neighbourhood of the closed
ball with `f c ≠ 0` (the situation of the density plan). -/
theorem AnalyticOnNhd.circleAverage_log_norm_le_half_log_circleAverage_sq (c : ℂ) (R : ℝ)
    (hR : 0 < R) (f : ℂ → ℂ) (h₁f : AnalyticOnNhd ℂ f (Metric.closedBall c R)) (h₂f : f c ≠ 0) :
    circleAverage (fun z => Real.log ‖f z‖) c R
      ≤ (1/2) * Real.log (circleAverage (fun z => ‖f z‖ ^ 2) c R) :=
  circleAverage_log_norm_le_half_log_circleAverage_sq_of_ae c R hR f
    (h₁f.mono sphere_subset_closedBall).continuousOn
    ((h₁f.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm_of_nonneg hR.le)
    (h₁f.ae_circleMap_ne_zero c R hR f h₂f)
