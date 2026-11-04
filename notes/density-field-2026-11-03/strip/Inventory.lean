/- Inventory check: every name cited in the zero-density inventory report resolves at this pin
   (Lean v4.33.0-rc2, Mathlib 51e6992e), and the key tree theorems are sorry-free. Read-only. -/
import Zeta23.BL.BohrLandauClosure
import Zeta23.BL.DPMVexp

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta ArithmeticFunction.sigma LSeries.notation

-- (1) MV
#check @Zeta23.MVDiag
#check @Zeta23.MVHilbert
#check Zeta23.MV.mvDiag_thirteen
#check Zeta23.MV.mv_hilbert
#check @Zeta23.MVHilbert_of_diag
#check @Zeta23.MV.Adm
#check @Zeta23.MV.EigenBound
#check @Zeta23.MV.mvDiag_of_eigenBound
#print axioms Zeta23.MV.mvDiag_thirteen

-- (4) M1 / DPMV
#check @M1.log_nat_gap
#check @M1.mv_Icc
#check @M1.dirichlet_meanSquare_le
#check @M1.meanValue_pow_raw
#check @M1.meanValue_pow
#check @M1.meanValue_pow_logfree
#check @M1.meanValue_pow_explicit
#check @M1.sum_weight_le
#check @M1.sum_weight_le_logfree
#check @M1.sum_rpow_neg_le
#check @M1.sum_inv_le
#check @DPMV.dirichlet_mean_value
#check @DPMV2.dirichlet_mean_value
#check @Zeta23.BL.M3.Dpoly
#check @Zeta23.BL.M3.meanValue_Dpoly
#check @Zeta23.BL.M3.integral_bound_abstract
#check @Zeta23.BL.M3.MeanSquareUnifFrom
#print axioms M1.dirichlet_meanSquare_le

-- (2) Jensen chain
#check @sum_divisor_mul_log_le
#check @AnalyticOnNhd.circleAverage_log_norm_le_half_log_circleAverage_sq
#check @Zeta23.BL.count_disc_le
#check @Zeta23.BL.divisor_riemannZeta_eq
#check @Zeta23.BL.finset_sum_zeta_order_le_finsum_divisor
#check @Zeta23.BL.count_finset_le
#check @Zeta23.BL.Lz
#check @Zeta23.BL.circleAverage_Lz_le
#check @Zeta23.BL.count_window_le
#check @Zeta23.BL.integral_Lz_circle_le
#check @Zeta23.BL.integral_circleAverage_Lz_le
#check @Zeta23.BL.count_le_integral
#check @Zeta23.BL.count_le_meanSquare
#check @Zeta23.BL.count_le_meanSquare'
#check @Zeta23.BL.rightHalf_of_meanSquareUnif
#check @Zeta23.RvM.analyticOnNhd_riemannZeta
#check Zeta23.RvM.zeta_lower_bound_two
#check @Zeta23.RvM.riemannZeta_ne_zero_of_two_le_re
#check @Zeta23.analyticOrderAt_riemannZeta_ne_top
#check @MNF.RH.analyticAt_riemannZeta
#check @MeromorphicOn.divisor_mul
#check @MeromorphicOn.divisor_fun_mul
#check @analyticOrderAt_mul
#check @MeromorphicOn.AnalyticOnNhd.divisor_apply
#check @MeromorphicOn.AnalyticOnNhd.divisor_nonneg
#check @AnalyticOnNhd.circleAverage_log_norm
#print axioms Zeta23.BL.count_le_meanSquare'
#print axioms Zeta23.BL.bohrLandau_full
#print axioms BLClosure.meanSquareUnif_all
#print axioms BLClosure.zeta_approx_sharp
#print axioms Zeta23.BL.bohrLandau   -- the sorried scoping theorem of Zeta23/BohrLandau.lean

-- (3) Mathlib arithmetic
#check @ArithmeticFunction.moebius
#check @ArithmeticFunction.moebius_mul_coe_zeta
#check @ArithmeticFunction.coe_zeta_mul_coe_moebius
#check @ArithmeticFunction.coe_moebius_mul_coe_zeta
#check @ArithmeticFunction.one_apply
#check @ArithmeticFunction.mul_apply
#check @ArithmeticFunction.coe_zeta_mul_apply
#check @ArithmeticFunction.coe_mul_zeta_apply
#check @ArithmeticFunction.IsMultiplicative
#check @ArithmeticFunction.IsMultiplicative.mul
#check ArithmeticFunction.isMultiplicative_moebius
#check ArithmeticFunction.isMultiplicative_zeta
#check @ArithmeticFunction.isMultiplicative_sigma
#check @ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
#check @ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq
#check @ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on
#check @ArithmeticFunction.prod_eq_iff_prod_pow_moebius_eq
#check @ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
#check @ArithmeticFunction.abs_moebius_le_one
#check @ArithmeticFunction.moebius_sq
#check @ArithmeticFunction.sigma_zero_apply
#check @ArithmeticFunction.sigma_zero_apply_prime_pow
#check @Nat.card_divisors
#check @Nat.card_divisors_le_self
#check @Nat.Coprime.card_divisors_mul
#check @Nat.sum_divisorsAntidiagonal
#check @Nat.sum_divisorsAntidiagonal'
#check @Nat.mem_divisorsAntidiagonal
#check @Nat.mem_divisors
#check @Nat.sum_divisors_eq_sum_properDivisors_add_self
#check @Nat.divisors_mul
#check @Finset.nat_divisors_prod
#check @harmonic_eq_sum_Icc
#check @harmonic_le_one_add_log
#check @log_add_one_le_harmonic
#check @harmonic_floor_le_one_add_log
#check @LSeries_zeta_mul_Lseries_moebius
#check @LSeries_zeta_eq_riemannZeta
#check @LSeries_convolution'
#check @LSeries_mul'
#check @LSeries.convolution_def
#check @LSeriesSummable_moebius_iff
#check @sum_mul_eq_sub_sub_integral_mul
#check @ArithmeticFunction.vonMangoldt_sum
#check @ArithmeticFunction.sum_moebius_mul_log_eq
#check @Finset.sum_mul_sq_le_sq_mul_sq

-- the pointwise Möbius identity Σ_{d ∣ n} μ d = [n = 1], assembled from the three Mathlib lemmas
example (n : ℕ) : (∑ d ∈ n.divisors, μ d) = if n = 1 then 1 else 0 := by
  rw [← ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.coe_zeta_mul_moebius,
    ArithmeticFunction.one_apply]
