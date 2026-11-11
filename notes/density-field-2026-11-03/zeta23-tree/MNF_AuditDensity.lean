/- Audit of the density layer on the zeta23 tree: axiom reports and printed statements for every
   theorem the Comparator challenge names. Compiled by z23_density_report.sh with plain `lean`,
   sandboxed, against the tree Comparator built. -/
import MNF.RH.DensityAll

#print axioms MNF.RH.N0_le_Ncount
#print axioms MNF.RH.NOff_le_Ncount
#print axioms MNF.RH.gap_forces_NOff_eq
#print axioms MNF.RH.on_line_density_one_of_gap
#print axioms MNF.RH.nullify_eq_zero_iff
#print axioms MNF.RH.NNear_eq_nullified_count
#print axioms MNF.RH.Ncount_eq_near_add_off
#print axioms MNF.RH.N0_le_NNear
#print axioms MNF.RH.NOff_le_NOffLine
#print axioms MNF.RH.NNear_eq_N0_of_gap
#print axioms MNF.RH.ncountSuperlinear
#print axioms MNF.RH.offLine_le_one_third
#print axioms MNF.RH.NOff_le_one_third
#print axioms MNF.RH.reservoirDensityOne_of_bohrLandau
#print axioms MNF.RH.near_line_density_one
#print axioms MNF.RH.nullified_density_one
#print axioms MNF.RH.onLineDensityOne_of_reservoir_of_gap
#print axioms MNF.RH.onLineDensityOne_of_gap
#print axioms MNF.RH.NOff_eq_right_add_left
#print axioms MNF.RH.NLeft_eq_NRight
#print axioms MNF.RH.bohrLandau_of_right
#print axioms MNF.RH.onLineDensityOne_of_right
#print axioms MNF.RH.reservoirDensityOne_of_right
#print axioms MNF.Extension.conservation
#print axioms MNF.Extension.idempotent'
#print axioms MNF.Extension.dilation_covariance
#print axioms MNF.Extension.abs_nullify_antitone_in_threshold
#print axioms MNF.Extension.eject_gapped
#print axioms MNF.Extension.eject_idem
#print axioms MNF.Extension.nullify_eject
#print axioms MNF.Extension.eject_nullify
#print axioms MNF.Extension.remainder_eject
#print axioms MNF.Extension.eject_sub_nullify
#print axioms MNF.Extension.eject_probe_reading
#print axioms MNF.Extension.eject_dilation
#print axioms MNF.Extension.nullify_comp_nullify
#print axioms MNF.Extension.eject_comp_eject
#print axioms MNF.Extension.nullify_floor
#print axioms MNF.Extension.eject_ceiling
#print axioms MNF.Extension.deficit_deficit
#print axioms MNF.Extension.deficit_tripotent
#print axioms MNF.Extension.nullify_deficit
#print axioms MNF.Extension.northProbe_deficit
#print axioms MNF.Extension.eject_eq_id_add_deficit
#print axioms MNF.Extension.nullify_eq_id_sub_deficit_sq
#print axioms MNF.Extension.metricProj_branch
#print axioms MNF.Extension.metricProj_deficit_swap
#print axioms MNF.Extension.rep_conservation
#print axioms MNF.Extension.rep_not_distributive
#print axioms MNF.Extension.content_inject
#print axioms MNF.Extension.nu_inject
#print axioms MNF.Extension.eps_inject
#print axioms MNF.Extension.inject_nullified
#print axioms MNF.Extension.inject_at_kstar
#print axioms MNF.Extension.eventual_nullification
#print axioms MNF.Extension.typeA_on_demand
#print axioms MNF.Extension.compact_inject
#print axioms MNF.Extension.nullify_sees_through
#print axioms MNF.Extension.refine_inject
#print axioms MNF.Extension.ladder_not_composite
#print axioms MNF.Extension.deltaStar_singleton
#print axioms MNF.Extension.nu_eq_zero_of_all_below
#print axioms MNF.Extension.deltaStar_inject
#print axioms MNF.Extension.sameSign_refine_le
#print axioms MNF.Extension.sameSign_nu_le_content
#print axioms MNF.Extension.sameSign_sign
#print axioms MNF.Extension.mixed_refine_can_increase
#print axioms MNF.Extension.zero_reading_uninformative
#print axioms MNF.Extension.inProcess_ne_postHoc
#print axioms MNF.Extension.residue_eq
#print axioms MNF.Extension.two_piece_sign_safe
#print axioms MNF.Extension.residue_both_signs
#print axioms MNF.Extension.realise
#print axioms MNF.Extension.gate_minimax
#print axioms MNF.Extension.soft_idem_iff
#print axioms MNF.Extension.soft_no_gap
#print axioms MNF.Extension.hardGate_is_nullify
#print axioms MNF.Extension.injectAdd_ejectAdd
#print axioms MNF.Extension.ejectAdd_not_additive
#print axioms MNF.RH.nullify_eq_extension
#print axioms MNF.RH.mem_Band_iff_nullified
#print axioms MNF.RH.eject_fixed_iff_zero
#print axioms MNF.RH.eject_band_edge
#print axioms MNF.RH.eq_zero_iff_gapped_all
#print axioms MNF.RH.eq_zero_iff_eject_fixed_all
#print axioms MNF.RH.eq_zero_iff_nullified_all
#print axioms MNF.RH.displacement_injectable
#print axioms MNF.RH.injected_reads_zero_iff
#print axioms MNF.RH.band_injection_blind
#print axioms MNF.RH.trace_singleton
#print axioms MNF.RH.trace_zero
#print axioms MNF.RH.trace_inject_pos
#print axioms MNF.RH.trace_inject_tendsto
#print axioms MNF.RH.on_line_iff_eject_fixed_all
#print axioms MNF.RH.on_line_iff_nullified_all
#print axioms MNF.RH.on_line_iff_trace_zero
#print axioms MNF.RH.band_trivial_of_gap
#print axioms MNF.RH.gap_of_band_trivial
#print axioms DPMV.cpow_neg_mul_I_eq_exp
#print axioms DPMV.conj_cpow_neg_mul_I
#print axioms DPMV.prod_eq_exp
#print axioms DPMV.integral_exp_I_mul
#print axioms DPMV.integral_exp_I_mul_zero
#print axioms DPMV.norm_exp_I_mul_eq_one
#print axioms DPMV.norm_integral_exp_I_mul_le
#print axioms DPMV.J_self
#print axioms DPMV.norm_J_le
#print axioms DPMV.normSq_sum_expand
#print axioms DPMV.integral_normSq_sum
#print axioms DPMV.dirichlet_mean_value
#print axioms DPMV2.integral_exp_mul_I
#print axioms DPMV2.integral_exp_zero_mul_I
#print axioms DPMV2.norm_integral_exp_mul_I_le
#print axioms DPMV2.ofReal_norm_sq_dirichlet
#print axioms DPMV2.ofReal_integral_norm_sq_dirichlet
#print axioms DPMV2.log_sub_log_ne_zero
#print axioms DPMV2.norm_integral_freq_le
#print axioms DPMV2.sum_bound_split
#print axioms DPMV2.dirichlet_mean_value
#print axioms sum_divisor_mul_log_le
#print axioms circleAverage_log_norm_le_half_log_circleAverage_sq_of_ae
#print axioms circleAverage_log_norm_le_half_log_circleAverage_sq
#print axioms AnalyticOnNhd.ae_circleMap_ne_zero
#print axioms AnalyticOnNhd.circleAverage_log_norm_le_half_log_circleAverage_sq
#print axioms M1.log_nat_gap
#print axioms M1.mv_Icc
#print axioms M1.log_sub_log_ne_zero
#print axioms M1.term_eq
#print axioms M1.Z_eq
#print axioms M1.norm_cpow_neg_mul_I
#print axioms M1.dirichlet_meanSquare_le
#print axioms M1.cpow_neg_add_eq
#print axioms M1.norm_sq_rpow
#print axioms M1.sum_inv_le
#print axioms M1.sum_weight_le
#print axioms M1.meanValue_pow_raw
#print axioms M1.meanValue_pow
#print axioms M1.sum_Icc_rpow_le_integral
#print axioms M1.sum_rpow_neg_le
#print axioms M1.sum_Icc_rpow_le
#print axioms M1.sum_weight_le_logfree
#print axioms M1.meanValue_pow_logfree
#print axioms M1.meanValue_pow_explicit
#print axioms Zeta23.BL.M2.norm_add4_sq_le
#print axioms Zeta23.BL.M2.s_re
#print axioms Zeta23.BL.M2.s_im
#print axioms Zeta23.BL.M2.one_sub_s_re
#print axioms Zeta23.BL.M2.one_sub_s_im
#print axioms Zeta23.BL.M2.neg_s_re
#print axioms Zeta23.BL.M2.s_ne_one
#print axioms Zeta23.BL.M2.s_ne_zero
#print axioms Zeta23.BL.M2.norm_s_le
#print axioms Zeta23.BL.M2.norm_one_sub_s_ge
#print axioms Zeta23.BL.M2.rpow_sq_eq
#print axioms Zeta23.BL.M2.norm_P_le
#print axioms Zeta23.BL.M2.norm_P_le'
#print axioms Zeta23.BL.M2.norm_Q_le
#print axioms Zeta23.BL.M2.norm_Q_le'
#print axioms Zeta23.BL.M2.norm_R_le_core
#print axioms Zeta23.BL.M2.norm_R_le
#print axioms Zeta23.BL.M2.norm_R_le_uniform
#print axioms Zeta23.BL.M2.norm_R_le'
#print axioms Zeta23.BL.M2.zeta_eq_four_terms
#print axioms Zeta23.BL.M2.zeta_sub_sum_le
#print axioms Zeta23.BL.M2.norm_zeta_sq_le
#print axioms Zeta23.BL.M2.norm_zeta_sq_le'
#print axioms Zeta23.BL.M2.one_div_cpow_eq_rpow_mul
#print axioms Zeta23.BL.M2.range_sum_eq_Icc
#print axioms Zeta23.BL.M2.range_sum_eq_twist
#print axioms Zeta23.BL.M2.integral_range_sq_eq_Icc
#print axioms M3a.sum_Icc_one_eq
#print axioms M3a.antitoneOn_rpow_Icc
#print axioms M3a.sum_Ico_rpow_succ_le_integral
#print axioms M3a.sum_Icc_rpow_le
#print axioms M3a.sum_Icc_rpow_le_mul
#print axioms M3a.sum_Icc_rpow_le_tsum
#print axioms M3a.sum_Icc_rpow_neg_le_tsum_one_div
#print axioms M3a.sum_Icc_rpow_mul_log_le
#print axioms M3a.sum_Icc_rpow_mul_log_le_of_sigma
#print axioms M3a.sum_Icc_rpow_le_of_sigma
#print axioms Zeta23.BL.M3.continuous_Dpoly
#print axioms Zeta23.BL.M3.meanValue_Dpoly
#print axioms Zeta23.BL.M3.norm_zeta_sq_le_unif
#print axioms Zeta23.BL.M3.continuousOn_norm_zeta_sq
#print axioms Zeta23.BL.M3.integral_inv_sq_one
#print axioms Zeta23.BL.M3.integral_bound_abstract
#print axioms Zeta23.BL.M3.meanSquare_param
#print axioms Zeta23.BL.M3.N_choice
#print axioms Zeta23.BL.M3.rpow_neg_le_of_choice
#print axioms Zeta23.BL.M3.rpow_pos_le_of_choice
#print axioms Zeta23.BL.M3.meanSquareUnif_explicit
#print axioms Zeta23.BL.M3.meanSquareUnif_naive
#print axioms Zeta23.BL.M3.meanSquareUnif_task
#print axioms Zeta23.BL.NRight_eq_zero_of_half_le
#print axioms Zeta23.BL.MNF_zerosIn_union
#print axioms Zeta23.BL.NRight_add
#print axioms Zeta23.BL.NRight_sub_eq
#print axioms Zeta23.BL.NRight_mono
#print axioms Zeta23.BL.zeta_order_eq_zero_of_ne_zero
#print axioms Zeta23.BL.divisor_riemannZeta_eq_int
#print axioms Zeta23.BL.divisor_riemannZeta_eq
#print axioms Zeta23.BL.sum_zeta_order_le_finsum_divisor
#print axioms Zeta23.BL.finsum_divisor_riemannZeta_eq
#print axioms Zeta23.BL.finsum_divisor_riemannZeta_eq_zerosIn
#print axioms Zeta23.BL.mem_closedBall_iff_sq
#print axioms Zeta23.BL.abs_re_im_sub_le_of_mem_closedBall
#print axioms Zeta23.BL.bounds_of_mem_closedBall_two
#print axioms Zeta23.BL.one_notMem_closedBall_two
#print axioms Zeta23.BL.re_ge_of_mem_closedBall_Rout
#print axioms Zeta23.BL.outer_disc_facts
#print axioms Zeta23.BL.geom_facts
#print axioms Zeta23.BL.one_notMem_closedBall_two_add
#print axioms Zeta23.BL.one_notMem_sphere_two_add
#print axioms Zeta23.BL.neg_log_norm_riemannZeta_two_add_le
#print axioms Zeta23.BL.count_disc_le
#print axioms Zeta23.BL.finset_sum_zeta_order_le_finsum_divisor
#print axioms Zeta23.BL.count_finset_le
#print axioms Zeta23.BL.Lz_nonneg
#print axioms Zeta23.BL.log_le_half_log_one_add_sq
#print axioms Zeta23.BL.log_norm_le_Lz
#print axioms Zeta23.BL.continuousOn_Lz
#print axioms Zeta23.BL.circleIntegrable_Lz
#print axioms Zeta23.BL.circleAverage_log_norm_le_Lz
#print axioms Zeta23.BL.concaveOn_half_log_one_add
#print axioms Zeta23.BL.circleAverage_Lz_le
#print axioms Zeta23.BL.count_finset_le_log_meanSq
#print axioms Zeta23.BL.closedBall_Rout_subset
#print axioms Zeta23.BL.count_window_le
#print axioms Zeta23.BL.count_window_le_log_meanSq
#print axioms Zeta23.BL.circleAverage_log_le_Lz
#print axioms Zeta23.BL.circleMap_two_add
#print axioms Zeta23.BL.circleMap_two_add_ne_one
#print axioms Zeta23.BL.continuousOn_Lz_circleMap
#print axioms Zeta23.BL.integrableOn_Lz_circleMap_prod
#print axioms Zeta23.BL.integrable_Lz_circleMap_prod_restrict
#print axioms Zeta23.BL.intervalIntegrable_circleAverage_Lz
#print axioms Zeta23.BL.integral_circleAverage_Lz_eq_swap
#print axioms Zeta23.BL.Lz_le_half_sq
#print axioms Zeta23.BL.segment_mapsTo_ne_one
#print axioms Zeta23.BL.intervalIntegrable_Lz_segment
#print axioms Zeta23.BL.intervalIntegrable_normSq_zeta_segment
#print axioms Zeta23.BL.integral_Lz_circle_le
#print axioms Zeta23.BL.integral_circleAverage_Lz_le
#print axioms Zeta23.BL.count_le_integral
#print axioms Zeta23.BL.count_le_meanSquare
#print axioms Zeta23.BL.count_le_meanSquare'
#print axioms Zeta23.BL.tsum_one_div_rpow_anti
#print axioms Zeta23.BL.meanSquare_of_gt_one
#print axioms Zeta23.BL.meanSquare_hyp_extend
#print axioms Zeta23.BL.rightHalf_of_meanSquareUnif
#print axioms Zeta23.BL.rightHalf_gt_sixth
#print axioms Zeta23.BL.bohrLandau_gt_sixth
#print axioms Zeta23.BL.M45.norm_zeta_le_strip
#print axioms Zeta23.BL.M45.meanSquare_zero_one
#print axioms Zeta23.BL.M45.continuous_norm_zeta_sq
#print axioms Zeta23.BL.M45.zeta_one_lower
#print axioms Zeta23.BL.M45.not_intervalIntegrable_zeta_one_sq
#print axioms Zeta23.BL.M45.integral_zeta_one_sq_eq_zero
#print axioms Zeta23.BL.M45.meanSquare_one
#print axioms Zeta23.BL.M45.meanSquare_strip_lt_one
#print axioms Zeta23.BL.M45.meanSquare_one_from_one
#print axioms Zeta23.BL.M45.meanSquare_strip_of
#print axioms Zeta23.BL.M45.meanSquare_strip_from
#print axioms MNF.RH.rightHalf_gt_sixth
#print axioms MNF.RH.bohrLandau_gt_sixth
#print axioms MNF.RH.reservoirDensity_of_linear_bound
#print axioms MNF.RH.reservoirDensity_gt_sixth
#print axioms MNF.RH.near_line_density_gt_sixth
#print axioms MNF.RH.nullified_density_gt_sixth
#print axioms MNF.RH.onLineDensityOne_of_gap_gt_sixth
#print axioms BLClosure.hasSum_cos_div_sq_bernoulli
#print axioms BLClosure.cos_mode_fract
#print axioms BLClosure.B2per_fourier
#print axioms BLClosure.P_fourier
#print axioms BLClosure.P_nonpos
#print axioms BLClosure.P_intCast
#print axioms BLClosure.P_eq
#print axioms BLClosure.psi_abs_le
#print axioms BLClosure.P_abs_le
#print axioms BLClosure.P_natCast
#print axioms BLClosure.continuous_P
#print axioms BLClosure.measurable_psi
#print axioms BLClosure.hasDerivAt_P
#print axioms BLClosure.integrableOn_bdd_mul_cpow
#print axioms BLClosure.integrableOn_psi_mul
#print axioms BLClosure.integrableOn_P_mul
#print axioms BLClosure.tail_by_parts_interval
#print axioms BLClosure.tail_by_parts
#print axioms BLClosure.hasDerivAt_P'
#print axioms BLClosure.first_derivative_test_amp_smooth'
#print axioms BLClosure.first_derivative_test_amp_smooth
#print axioms BLClosure.first_derivative_test_smooth
#print axioms BLClosure.mode_integrand_eq
#print axioms BLClosure.mode_bound_interval
#print axioms BLClosure.integrableOn_bdd_mul_cpow'
#print axioms BLClosure.integrableOn_exp_mul_cpow
#print axioms BLClosure.integrableOn_exp_neg_mul_cpow
#print axioms BLClosure.re_w
#print axioms BLClosure.re_w_lt
#print axioms BLClosure.re_phase
#print axioms BLClosure.re_phase'
#print axioms BLClosure.tail_mode_bound'
#print axioms BLClosure.tail_mode_bound
#print axioms BLClosure.tail_mode_bound_neg
#print axioms BLClosure.cmode_hasSum
#print axioms BLClosure.continuous_cmode
#print axioms BLClosure.cmode_abs_le
#print axioms BLClosure.cmode_eq
#print axioms BLClosure.mode_integral_bound
#print axioms BLClosure.hasSum_mode_integrals
#print axioms BLClosure.split_P
#print axioms BLClosure.integral_cpow_tail
#print axioms BLClosure.tail_sharp
#print axioms BLClosure.zeta_eq_euler_maclaurin
#print axioms BLClosure.norm_natCast_cpow_neg_div_two
#print axioms BLClosure.zeta_approx_sharp
#print axioms BLClosure.zeta_approx_sharp_segment
#print axioms BLClosure.zeta_approx_sharp_segment'
#print axioms BLClosure.S_eq_Dpoly
#print axioms BLClosure.norm_main_term_le
#print axioms BLClosure.norm_zeta_sq_le_sharp
#print axioms BLClosure.meanSquare_sharp_param
#print axioms BLClosure.meanSquareUnif_all_of_lt_one
#print axioms BLClosure.meanSquareUnif_all
#print axioms BLClosure.meanSquareUnifFrom_all
#print axioms BLClosure.rightHalfBound
#print axioms BLClosure.bohrLandau_all
#print axioms Zeta23.BL.rightHalf_all
#print axioms Zeta23.BL.rightHalfBound
#print axioms Zeta23.BL.bohrLandau_full
#print axioms Zeta23.BL.rightHalfBound_of_meanSquare'
#print axioms Zeta23.BL.meanSquare_strip'
#print axioms MNF.RH.reservoirDensityOne_unconditional
#print axioms MNF.RH.onLineDensityOne_of_gap_only
#print axioms Zeta23.BL.one_half_pos'
#print axioms Zeta23.BL.tsum_one_div_rpow_two_sq_le
#print axioms Zeta23.BL.meanSquare_explicit_small
#print axioms Zeta23.BL.NRight_le_Ncount
#print axioms Zeta23.BL.Rout_half
#print axioms Zeta23.BL.rin_half
#print axioms Zeta23.BL.hwin_half_ge
#print axioms Zeta23.BL.log_half_ge
#print axioms Zeta23.BL.K_half_ge
#print axioms Zeta23.BL.rpow_neg_five_half_mul
#print axioms Zeta23.BL.log_three_nonneg
#print axioms Zeta23.BL.bohrLandau_explicit
#print axioms Zeta23.MNF_Ncount_le_mul_log
#print axioms Zeta23.MNF_mul_log_le_Ncount
#print axioms MNF.RH.abs_re_sub_half_lt_half
#print axioms MNF.RH.abs_re_sub_half_le_half
#print axioms MNF.RH.NOff_anti
#print axioms MNF.RH.NOff_antitone
#print axioms MNF.RH.NOff_intervalIntegrable
#print axioms MNF.RH.indicator_le_antitone
#print axioms MNF.RH.term_intervalIntegrable
#print axioms MNF.RH.integral_indicator_le_eq
#print axioms MNF.RH.reservoirMass_eq_integral
#print axioms MNF.RH.reservoirMass_nonneg
#print axioms MNF.RH.reservoirMass_le_half_Ncount
#print axioms MNF.RH.integral_NOff_split
#print axioms MNF.RH.integral_NOff_le_mul_Ncount
#print axioms MNF.RH.integral_NOff_tail_le
#print axioms MNF.RH.reservoirMass_le_split
#print axioms MNF.RH.reservoirMass_le_eps_Ncount
#print axioms MNF.RH.signedReservoir_eq_zero
#print axioms MNF.RH.sum_right_eq_sum_left
#print axioms MNF.RH.reservoirMass_eq_two_right
#print axioms MNF.RH.rpow_tail_intervalIntegrable
#print axioms MNF.RH.integral_rpow_tail_le
#print axioms MNF.RH.reservoirMass_le_rpow
#print axioms MNF.RH.reservoirMass_le_Ncount_mul
#print axioms MNF.RH.meanDisplacement_tendsto_zero
#print axioms Zeta23.Density.analyticOnNhd_Mx
#print axioms Zeta23.Density.analyticOnNhd_fz
#print axioms Zeta23.Density.continuousOn_fz
#print axioms Zeta23.Density.tail_inv_sq_le
#print axioms Zeta23.Density.fz_sub_one_eq
#print axioms Zeta23.Density.norm_fz_sub_one_le
#print axioms Zeta23.Density.pi_sq_lt_ten
#print axioms Zeta23.Density.pi_sq_div_six_div_le
#print axioms Zeta23.Density.norm_fz_le_one_add
#print axioms Zeta23.Density.one_sub_norm_le_norm_fz
#print axioms Zeta23.Density.fz_lower_two
#print axioms Zeta23.Density.neg_log_norm_fz_two_le
#print axioms Zeta23.Density.log_norm_fz_le_of_two_le_re
#print axioms Zeta23.Density.norm_sq_fz_le_of_two_le_re
#print axioms Zeta23.Density.abs_cm_le
#print axioms Zeta23.Density.cm_eq_of_le
#print axioms Zeta23.Density.S_mul_Mx_eq
#print axioms Zeta23.Density.card_filter_dvd_dvd_le
#print axioms Zeta23.Density.gcd_le_sum_dvd
#print axioms Zeta23.Density.gcd_le_sum_Icc
#print axioms Zeta23.Density.sum_div_of_dvd_le
#print axioms Zeta23.Density.ite_and_div_eq
#print axioms Zeta23.Density.sum_gcd_div_le
#print axioms Zeta23.Density.dX_eq_card_filter
#print axioms Zeta23.Density.dX_eq_sum
#print axioms Zeta23.Density.sum_dX_sq_le
#print axioms Zeta23.Density.sum_mul_le_of_partial_sums
#print axioms Zeta23.Density.sum_mul_le_of_partial_sums_tail
#print axioms Zeta23.Density.sum_Ioc_rpow_le
#print axioms Zeta23.Density.tail_sum_le
#print axioms Zeta23.Density.weight_sum_le
#print axioms Zeta23.Density.integral_window_eq
#print axioms Zeta23.Density.norm_coeff_sq
#print axioms Zeta23.Density.abs_cm_sq_le
#print axioms Zeta23.Density.meanSquare_prodPoly
#print axioms Zeta23.Density.norm_add_sq_le_eta
#print axioms Zeta23.Density.norm_Mx_le
#print axioms Zeta23.Density.continuousOn_B_window
#print axioms Zeta23.Density.integral_inv_sq_window
#print axioms Zeta23.Density.meanSquare_B_window
#print axioms Zeta23.Density.continuous_A_window
#print axioms Zeta23.Density.continuousOn_fz_window
#print axioms Zeta23.Density.meanSquare_fz_window
#print axioms Zeta23.Density.sum_Icc_two_inv_mul_sub_one
#print axioms Zeta23.Density.norm_moebius_mul_cpow_le
#print axioms Zeta23.Density.Mx_eq_one_add
#print axioms Zeta23.Density.Mx_ne_zero_of_le_re
#print axioms Zeta23.Density.analyticOrderAt_Mx_ne_top
#print axioms Zeta23.Density.zeta_order_le_divisor_fz
#print axioms Zeta23.Density.finset_sum_zeta_order_le_finsum_divisor_fz
#print axioms Zeta23.Density.fz_two_add_ne_zero
#print axioms Zeta23.Density.count_disc_le_fz
#print axioms Zeta23.Density.count_finset_le_fz
#print axioms Zeta23.Density.count_window_le_fz
#print axioms Zeta23.Density.log_norm_le_Leps
#print axioms Zeta23.Density.continuousOn_Leps
#print axioms Zeta23.Density.circleAverage_log_norm_le_Leps
#print axioms Zeta23.Density.concaveOn_half_log_add
#print axioms Zeta23.Density.half_log_le_half
#print axioms Zeta23.Density.segment_average_Leps_le
#print axioms Zeta23.Density.continuousOn_Leps_fz_ne_one
#print axioms Zeta23.Density.continuousOn_Leps_circleMap
#print axioms Zeta23.Density.integrableOn_Leps_circleMap_prod
#print axioms Zeta23.Density.integrable_Leps_circleMap_prod_restrict
#print axioms Zeta23.Density.intervalIntegrable_circleAverage_Leps
#print axioms Zeta23.Density.integral_circleAverage_Leps_eq_swap
#print axioms Zeta23.Density.intervalIntegrable_Leps_segment
#print axioms Zeta23.Density.intervalIntegrable_normSq_fz_segment
#print axioms Zeta23.Density.circleAverage_log_fz_le_Leps
#print axioms Zeta23.Density.count_le_integral_fz_window
#print axioms Zeta23.Density.count_le_integral_fz_NSigma
#print axioms Zeta23.Density.NRight_sub_eq_NSigma
#print axioms Zeta23.Density.count_le_integral_fz
#print axioms Zeta23.Density.integral_Leps_segment_le_of_meanSquare
#print axioms Zeta23.Density.Leps_fz_le_of_two_le_re
#print axioms Zeta23.Density.integral_Leps_segment_le_of_two_le
#print axioms Zeta23.Density.integral_Leps_circle_le
#print axioms Zeta23.Density.integral_circleAverage_Leps_le
#print axioms Zeta23.Density.count_le_meanSquare_fz_window
#print axioms Zeta23.Density.count_le_meanSquare_fz
#print axioms Zeta23.Density.theta_pos
#print axioms Zeta23.Density.theta_le_one
#print axioms Zeta23.Density.kappa_pos
#print axioms Zeta23.Density.kappa_le_theta
#print axioms Zeta23.Density.theta_mul_eq
#print axioms Zeta23.Density.offdiag_exponent
#print axioms Zeta23.Density.cross_exponent
#print axioms Zeta23.Density.cross_exponent'
#print axioms Zeta23.Density.half_le_nat_floor
#print axioms Zeta23.Density.rpow_sq_eq
#print axioms Zeta23.Density.two_rpow_le_two
#print axioms Zeta23.Density.one_add_log_cube_le_rpow
#print axioms Zeta23.Density.single_params
#print axioms Zeta23.Density.X_rpow_le
#print axioms Zeta23.Density.rpow_le_X_rpow
#print axioms Zeta23.Density.NX_rpow_div_le
#print axioms Zeta23.Density.inv_X_le
#print axioms Zeta23.Density.E0gen_le
#print axioms Zeta23.Density.le_E0gen
#print axioms Zeta23.Density.E0gen_le_const
#print axioms Zeta23.Density.cross_le
#print axioms Zeta23.Density.Egen_le
#print axioms Zeta23.Density.Ksingle_pos
#print axioms Zeta23.Density.exponent_single
#print axioms Zeta23.Density.w4_rhs_le
#print axioms Zeta23.Density.geom_lower
#print axioms Zeta23.Density.count_le_Egen
#print axioms Zeta23.Density.density_single_window
#print axioms MNF.RH.mirror_re
#print axioms MNF.RH.mirror_im
#print axioms MNF.RH.mirror_mirror
#print axioms MNF.RH.mirror_injective
#print axioms MNF.RH.is_nontrivial_zero_mirror
#print axioms MNF.RH.mirror_mem_zerosIn
#print axioms MNF.RH.zeta_order_mirror
#print axioms MNF.RH.is_nontrivial_zero_conj
#print axioms MNF.RH.mirror_eq_self_iff
#print axioms MNF.RH.one_le_zeta_order
#print axioms MNF.RH.inBand_or_inReservoir_or_onLine
#print axioms MNF.RH.inBand_mirror_iff
#print axioms MNF.RH.mem_bandZeros_mirror
#print axioms MNF.RH.degenerate_of_not_onLine
#print axioms MNF.RH.onLine_and_simple_of_not_degenerate
#print axioms MNF.RH.not_degenerate_of_onLine_simple
#print axioms MNF.RH.noDegenerate_iff
#print axioms MNF.RH.spectralGapHyp_iff_not_inBand
#print axioms MNF.RH.spectralGapHyp_iff_ordinatesInjectiveOn_bandZeros
#print axioms MNF.RH.bandCoincidentMass_eq_zero_of_spectralGapHyp
#print axioms MNF.RH.not_inBand_of_bandCoincidentMass_eq_zero
#print axioms MNF.RH.spectralGapHyp_iff_bandCoincidentMass_of_im_ne_zero
#print axioms MNF.RH.zeta_em_remainder_norm_le
#print axioms MNF.RH.riemannZeta_ofReal_ne_zero_of_mem_Ioo
#print axioms MNF.RH.nontrivial_zero_im_ne_zero
#print axioms MNF.RH.spectralGapHyp_iff_bandCoincidentMass
#print axioms MNF.RH.bandCoincidentMass_nonneg
#print axioms MNF.RH.bandCoincidentMass_le_offDiagonalCoincidentMass
#print axioms MNF.RH.finsum_mem_inter_setOf_eq_sum_filter
#print axioms MNF.RH.NOffLine_real_eq_sum_filter
#print axioms MNF.RH.N0_real_eq_sum_filter
#print axioms MNF.RH.Ncount_eq_N0_add_NOffLine
#print axioms MNF.RH.pairSum_eq_sum
#print axioms MNF.RH.pairSum_const
#print axioms MNF.RH.pairSum_fst
#print axioms MNF.RH.pairSum_snd
#print axioms MNF.RH.pairSum_fst_indicator
#print axioms MNF.RH.pairSum_fst_abs
#print axioms MNF.RH.pairSum_fst_abs_eq_integral
#print axioms MNF.RH.pairSum_swap
#print axioms MNF.RH.pairSum_nonneg
#print axioms MNF.RH.pairSum_mono
#print axioms MNF.RH.diagonalMass_nonneg
#print axioms MNF.RH.diagonalMass_le_sq_Ncount
#print axioms MNF.RH.Ncount_le_diagonalMass
#print axioms MNF.RH.coincidentMass_eq
#print axioms MNF.RH.offDiagonalCoincidentMass_nonneg
#print axioms MNF.RH.offLine_sq_le_offDiagonalCoincidentMass
#print axioms MNF.RH.offDiagonalCoincidentMass_le
#print axioms MNF.RH.offDiagonalCoincidentMass_le_two_mul
#print axioms MNF.RH.offDiagonalCoincidentMass_eq_zero_of_onLine
#print axioms MNF.RH.onLine_of_offDiagonalCoincidentMass_eq_zero
#print axioms MNF.RH.offDiagonalCoincidentMass_le_two_thirds
#print axioms MNF.RH.offDiagonalCoincidentMass_le_five_ninths

#check @MNF.RH.N0_le_Ncount
#check @MNF.RH.NOff_le_Ncount
#check @MNF.RH.gap_forces_NOff_eq
#check @MNF.RH.on_line_density_one_of_gap
#check @MNF.RH.nullify_eq_zero_iff
#check @MNF.RH.NNear_eq_nullified_count
#check @MNF.RH.Ncount_eq_near_add_off
#check @MNF.RH.N0_le_NNear
#check @MNF.RH.NOff_le_NOffLine
#check @MNF.RH.NNear_eq_N0_of_gap
#check @MNF.RH.ncountSuperlinear
#check @MNF.RH.offLine_le_one_third
#check @MNF.RH.NOff_le_one_third
#check @MNF.RH.reservoirDensityOne_of_bohrLandau
#check @MNF.RH.near_line_density_one
#check @MNF.RH.nullified_density_one
#check @MNF.RH.onLineDensityOne_of_reservoir_of_gap
#check @MNF.RH.onLineDensityOne_of_gap
#check @MNF.RH.NOff_eq_right_add_left
#check @MNF.RH.NLeft_eq_NRight
#check @MNF.RH.bohrLandau_of_right
#check @MNF.RH.onLineDensityOne_of_right
#check @MNF.RH.reservoirDensityOne_of_right
#check @MNF.Extension.conservation
#check @MNF.Extension.idempotent'
#check @MNF.Extension.dilation_covariance
#check @MNF.Extension.abs_nullify_antitone_in_threshold
#check @MNF.Extension.eject_gapped
#check @MNF.Extension.eject_idem
#check @MNF.Extension.nullify_eject
#check @MNF.Extension.eject_nullify
#check @MNF.Extension.remainder_eject
#check @MNF.Extension.eject_sub_nullify
#check @MNF.Extension.eject_probe_reading
#check @MNF.Extension.eject_dilation
#check @MNF.Extension.nullify_comp_nullify
#check @MNF.Extension.eject_comp_eject
#check @MNF.Extension.nullify_floor
#check @MNF.Extension.eject_ceiling
#check @MNF.Extension.deficit_deficit
#check @MNF.Extension.deficit_tripotent
#check @MNF.Extension.nullify_deficit
#check @MNF.Extension.northProbe_deficit
#check @MNF.Extension.eject_eq_id_add_deficit
#check @MNF.Extension.nullify_eq_id_sub_deficit_sq
#check @MNF.Extension.metricProj_branch
#check @MNF.Extension.metricProj_deficit_swap
#check @MNF.Extension.rep_conservation
#check @MNF.Extension.rep_not_distributive
#check @MNF.Extension.content_inject
#check @MNF.Extension.nu_inject
#check @MNF.Extension.eps_inject
#check @MNF.Extension.inject_nullified
#check @MNF.Extension.inject_at_kstar
#check @MNF.Extension.eventual_nullification
#check @MNF.Extension.typeA_on_demand
#check @MNF.Extension.compact_inject
#check @MNF.Extension.nullify_sees_through
#check @MNF.Extension.refine_inject
#check @MNF.Extension.ladder_not_composite
#check @MNF.Extension.deltaStar_singleton
#check @MNF.Extension.nu_eq_zero_of_all_below
#check @MNF.Extension.deltaStar_inject
#check @MNF.Extension.sameSign_refine_le
#check @MNF.Extension.sameSign_nu_le_content
#check @MNF.Extension.sameSign_sign
#check @MNF.Extension.mixed_refine_can_increase
#check @MNF.Extension.zero_reading_uninformative
#check @MNF.Extension.inProcess_ne_postHoc
#check @MNF.Extension.residue_eq
#check @MNF.Extension.two_piece_sign_safe
#check @MNF.Extension.residue_both_signs
#check @MNF.Extension.realise
#check @MNF.Extension.gate_minimax
#check @MNF.Extension.soft_idem_iff
#check @MNF.Extension.soft_no_gap
#check @MNF.Extension.hardGate_is_nullify
#check @MNF.Extension.injectAdd_ejectAdd
#check @MNF.Extension.ejectAdd_not_additive
#check @MNF.RH.nullify_eq_extension
#check @MNF.RH.mem_Band_iff_nullified
#check @MNF.RH.eject_fixed_iff_zero
#check @MNF.RH.eject_band_edge
#check @MNF.RH.eq_zero_iff_gapped_all
#check @MNF.RH.eq_zero_iff_eject_fixed_all
#check @MNF.RH.eq_zero_iff_nullified_all
#check @MNF.RH.displacement_injectable
#check @MNF.RH.injected_reads_zero_iff
#check @MNF.RH.band_injection_blind
#check @MNF.RH.trace_singleton
#check @MNF.RH.trace_zero
#check @MNF.RH.trace_inject_pos
#check @MNF.RH.trace_inject_tendsto
#check @MNF.RH.on_line_iff_eject_fixed_all
#check @MNF.RH.on_line_iff_nullified_all
#check @MNF.RH.on_line_iff_trace_zero
#check @MNF.RH.band_trivial_of_gap
#check @MNF.RH.gap_of_band_trivial
#check @DPMV.cpow_neg_mul_I_eq_exp
#check @DPMV.conj_cpow_neg_mul_I
#check @DPMV.prod_eq_exp
#check @DPMV.integral_exp_I_mul
#check @DPMV.integral_exp_I_mul_zero
#check @DPMV.norm_exp_I_mul_eq_one
#check @DPMV.norm_integral_exp_I_mul_le
#check @DPMV.J_self
#check @DPMV.norm_J_le
#check @DPMV.normSq_sum_expand
#check @DPMV.integral_normSq_sum
#check @DPMV.dirichlet_mean_value
#check @DPMV2.integral_exp_mul_I
#check @DPMV2.integral_exp_zero_mul_I
#check @DPMV2.norm_integral_exp_mul_I_le
#check @DPMV2.ofReal_norm_sq_dirichlet
#check @DPMV2.ofReal_integral_norm_sq_dirichlet
#check @DPMV2.log_sub_log_ne_zero
#check @DPMV2.norm_integral_freq_le
#check @DPMV2.sum_bound_split
#check @DPMV2.dirichlet_mean_value
#check @sum_divisor_mul_log_le
#check @circleAverage_log_norm_le_half_log_circleAverage_sq_of_ae
#check @circleAverage_log_norm_le_half_log_circleAverage_sq
#check @AnalyticOnNhd.ae_circleMap_ne_zero
#check @AnalyticOnNhd.circleAverage_log_norm_le_half_log_circleAverage_sq
#check @M1.log_nat_gap
#check @M1.mv_Icc
#check @M1.log_sub_log_ne_zero
#check @M1.term_eq
#check @M1.Z_eq
#check @M1.norm_cpow_neg_mul_I
#check @M1.dirichlet_meanSquare_le
#check @M1.cpow_neg_add_eq
#check @M1.norm_sq_rpow
#check @M1.sum_inv_le
#check @M1.sum_weight_le
#check @M1.meanValue_pow_raw
#check @M1.meanValue_pow
#check @M1.sum_Icc_rpow_le_integral
#check @M1.sum_rpow_neg_le
#check @M1.sum_Icc_rpow_le
#check @M1.sum_weight_le_logfree
#check @M1.meanValue_pow_logfree
#check @M1.meanValue_pow_explicit
#check @Zeta23.BL.M2.norm_add4_sq_le
#check @Zeta23.BL.M2.s_re
#check @Zeta23.BL.M2.s_im
#check @Zeta23.BL.M2.one_sub_s_re
#check @Zeta23.BL.M2.one_sub_s_im
#check @Zeta23.BL.M2.neg_s_re
#check @Zeta23.BL.M2.s_ne_one
#check @Zeta23.BL.M2.s_ne_zero
#check @Zeta23.BL.M2.norm_s_le
#check @Zeta23.BL.M2.norm_one_sub_s_ge
#check @Zeta23.BL.M2.rpow_sq_eq
#check @Zeta23.BL.M2.norm_P_le
#check @Zeta23.BL.M2.norm_P_le'
#check @Zeta23.BL.M2.norm_Q_le
#check @Zeta23.BL.M2.norm_Q_le'
#check @Zeta23.BL.M2.norm_R_le_core
#check @Zeta23.BL.M2.norm_R_le
#check @Zeta23.BL.M2.norm_R_le_uniform
#check @Zeta23.BL.M2.norm_R_le'
#check @Zeta23.BL.M2.zeta_eq_four_terms
#check @Zeta23.BL.M2.zeta_sub_sum_le
#check @Zeta23.BL.M2.norm_zeta_sq_le
#check @Zeta23.BL.M2.norm_zeta_sq_le'
#check @Zeta23.BL.M2.one_div_cpow_eq_rpow_mul
#check @Zeta23.BL.M2.range_sum_eq_Icc
#check @Zeta23.BL.M2.range_sum_eq_twist
#check @Zeta23.BL.M2.integral_range_sq_eq_Icc
#check @M3a.sum_Icc_one_eq
#check @M3a.antitoneOn_rpow_Icc
#check @M3a.sum_Ico_rpow_succ_le_integral
#check @M3a.sum_Icc_rpow_le
#check @M3a.sum_Icc_rpow_le_mul
#check @M3a.sum_Icc_rpow_le_tsum
#check @M3a.sum_Icc_rpow_neg_le_tsum_one_div
#check @M3a.sum_Icc_rpow_mul_log_le
#check @M3a.sum_Icc_rpow_mul_log_le_of_sigma
#check @M3a.sum_Icc_rpow_le_of_sigma
#check @Zeta23.BL.M3.continuous_Dpoly
#check @Zeta23.BL.M3.meanValue_Dpoly
#check @Zeta23.BL.M3.norm_zeta_sq_le_unif
#check @Zeta23.BL.M3.continuousOn_norm_zeta_sq
#check @Zeta23.BL.M3.integral_inv_sq_one
#check @Zeta23.BL.M3.integral_bound_abstract
#check @Zeta23.BL.M3.meanSquare_param
#check @Zeta23.BL.M3.N_choice
#check @Zeta23.BL.M3.rpow_neg_le_of_choice
#check @Zeta23.BL.M3.rpow_pos_le_of_choice
#check @Zeta23.BL.M3.meanSquareUnif_explicit
#check @Zeta23.BL.M3.meanSquareUnif_naive
#check @Zeta23.BL.M3.meanSquareUnif_task
#check @Zeta23.BL.NRight_eq_zero_of_half_le
#check @Zeta23.BL.MNF_zerosIn_union
#check @Zeta23.BL.NRight_add
#check @Zeta23.BL.NRight_sub_eq
#check @Zeta23.BL.NRight_mono
#check @Zeta23.BL.zeta_order_eq_zero_of_ne_zero
#check @Zeta23.BL.divisor_riemannZeta_eq_int
#check @Zeta23.BL.divisor_riemannZeta_eq
#check @Zeta23.BL.sum_zeta_order_le_finsum_divisor
#check @Zeta23.BL.finsum_divisor_riemannZeta_eq
#check @Zeta23.BL.finsum_divisor_riemannZeta_eq_zerosIn
#check @Zeta23.BL.mem_closedBall_iff_sq
#check @Zeta23.BL.abs_re_im_sub_le_of_mem_closedBall
#check @Zeta23.BL.bounds_of_mem_closedBall_two
#check @Zeta23.BL.one_notMem_closedBall_two
#check @Zeta23.BL.re_ge_of_mem_closedBall_Rout
#check @Zeta23.BL.outer_disc_facts
#check @Zeta23.BL.geom_facts
#check @Zeta23.BL.one_notMem_closedBall_two_add
#check @Zeta23.BL.one_notMem_sphere_two_add
#check @Zeta23.BL.neg_log_norm_riemannZeta_two_add_le
#check @Zeta23.BL.count_disc_le
#check @Zeta23.BL.finset_sum_zeta_order_le_finsum_divisor
#check @Zeta23.BL.count_finset_le
#check @Zeta23.BL.Lz_nonneg
#check @Zeta23.BL.log_le_half_log_one_add_sq
#check @Zeta23.BL.log_norm_le_Lz
#check @Zeta23.BL.continuousOn_Lz
#check @Zeta23.BL.circleIntegrable_Lz
#check @Zeta23.BL.circleAverage_log_norm_le_Lz
#check @Zeta23.BL.concaveOn_half_log_one_add
#check @Zeta23.BL.circleAverage_Lz_le
#check @Zeta23.BL.count_finset_le_log_meanSq
#check @Zeta23.BL.closedBall_Rout_subset
#check @Zeta23.BL.count_window_le
#check @Zeta23.BL.count_window_le_log_meanSq
#check @Zeta23.BL.circleAverage_log_le_Lz
#check @Zeta23.BL.circleMap_two_add
#check @Zeta23.BL.circleMap_two_add_ne_one
#check @Zeta23.BL.continuousOn_Lz_circleMap
#check @Zeta23.BL.integrableOn_Lz_circleMap_prod
#check @Zeta23.BL.integrable_Lz_circleMap_prod_restrict
#check @Zeta23.BL.intervalIntegrable_circleAverage_Lz
#check @Zeta23.BL.integral_circleAverage_Lz_eq_swap
#check @Zeta23.BL.Lz_le_half_sq
#check @Zeta23.BL.segment_mapsTo_ne_one
#check @Zeta23.BL.intervalIntegrable_Lz_segment
#check @Zeta23.BL.intervalIntegrable_normSq_zeta_segment
#check @Zeta23.BL.integral_Lz_circle_le
#check @Zeta23.BL.integral_circleAverage_Lz_le
#check @Zeta23.BL.count_le_integral
#check @Zeta23.BL.count_le_meanSquare
#check @Zeta23.BL.count_le_meanSquare'
#check @Zeta23.BL.tsum_one_div_rpow_anti
#check @Zeta23.BL.meanSquare_of_gt_one
#check @Zeta23.BL.meanSquare_hyp_extend
#check @Zeta23.BL.rightHalf_of_meanSquareUnif
#check @Zeta23.BL.rightHalf_gt_sixth
#check @Zeta23.BL.bohrLandau_gt_sixth
#check @Zeta23.BL.M45.norm_zeta_le_strip
#check @Zeta23.BL.M45.meanSquare_zero_one
#check @Zeta23.BL.M45.continuous_norm_zeta_sq
#check @Zeta23.BL.M45.zeta_one_lower
#check @Zeta23.BL.M45.not_intervalIntegrable_zeta_one_sq
#check @Zeta23.BL.M45.integral_zeta_one_sq_eq_zero
#check @Zeta23.BL.M45.meanSquare_one
#check @Zeta23.BL.M45.meanSquare_strip_lt_one
#check @Zeta23.BL.M45.meanSquare_one_from_one
#check @Zeta23.BL.M45.meanSquare_strip_of
#check @Zeta23.BL.M45.meanSquare_strip_from
#check @MNF.RH.rightHalf_gt_sixth
#check @MNF.RH.bohrLandau_gt_sixth
#check @MNF.RH.reservoirDensity_of_linear_bound
#check @MNF.RH.reservoirDensity_gt_sixth
#check @MNF.RH.near_line_density_gt_sixth
#check @MNF.RH.nullified_density_gt_sixth
#check @MNF.RH.onLineDensityOne_of_gap_gt_sixth
#check @BLClosure.hasSum_cos_div_sq_bernoulli
#check @BLClosure.cos_mode_fract
#check @BLClosure.B2per_fourier
#check @BLClosure.P_fourier
#check @BLClosure.P_nonpos
#check @BLClosure.P_intCast
#check @BLClosure.P_eq
#check @BLClosure.psi_abs_le
#check @BLClosure.P_abs_le
#check @BLClosure.P_natCast
#check @BLClosure.continuous_P
#check @BLClosure.measurable_psi
#check @BLClosure.hasDerivAt_P
#check @BLClosure.integrableOn_bdd_mul_cpow
#check @BLClosure.integrableOn_psi_mul
#check @BLClosure.integrableOn_P_mul
#check @BLClosure.tail_by_parts_interval
#check @BLClosure.tail_by_parts
#check @BLClosure.hasDerivAt_P'
#check @BLClosure.first_derivative_test_amp_smooth'
#check @BLClosure.first_derivative_test_amp_smooth
#check @BLClosure.first_derivative_test_smooth
#check @BLClosure.mode_integrand_eq
#check @BLClosure.mode_bound_interval
#check @BLClosure.integrableOn_bdd_mul_cpow'
#check @BLClosure.integrableOn_exp_mul_cpow
#check @BLClosure.integrableOn_exp_neg_mul_cpow
#check @BLClosure.re_w
#check @BLClosure.re_w_lt
#check @BLClosure.re_phase
#check @BLClosure.re_phase'
#check @BLClosure.tail_mode_bound'
#check @BLClosure.tail_mode_bound
#check @BLClosure.tail_mode_bound_neg
#check @BLClosure.cmode_hasSum
#check @BLClosure.continuous_cmode
#check @BLClosure.cmode_abs_le
#check @BLClosure.cmode_eq
#check @BLClosure.mode_integral_bound
#check @BLClosure.hasSum_mode_integrals
#check @BLClosure.split_P
#check @BLClosure.integral_cpow_tail
#check @BLClosure.tail_sharp
#check @BLClosure.zeta_eq_euler_maclaurin
#check @BLClosure.norm_natCast_cpow_neg_div_two
#check @BLClosure.zeta_approx_sharp
#check @BLClosure.zeta_approx_sharp_segment
#check @BLClosure.zeta_approx_sharp_segment'
#check @BLClosure.S_eq_Dpoly
#check @BLClosure.norm_main_term_le
#check @BLClosure.norm_zeta_sq_le_sharp
#check @BLClosure.meanSquare_sharp_param
#check @BLClosure.meanSquareUnif_all_of_lt_one
#check @BLClosure.meanSquareUnif_all
#check @BLClosure.meanSquareUnifFrom_all
#check @BLClosure.rightHalfBound
#check @BLClosure.bohrLandau_all
#check @Zeta23.BL.rightHalf_all
#check @Zeta23.BL.rightHalfBound
#check @Zeta23.BL.bohrLandau_full
#check @Zeta23.BL.rightHalfBound_of_meanSquare'
#check @Zeta23.BL.meanSquare_strip'
#check @MNF.RH.reservoirDensityOne_unconditional
#check @MNF.RH.onLineDensityOne_of_gap_only
#check @Zeta23.BL.one_half_pos'
#check @Zeta23.BL.tsum_one_div_rpow_two_sq_le
#check @Zeta23.BL.meanSquare_explicit_small
#check @Zeta23.BL.NRight_le_Ncount
#check @Zeta23.BL.Rout_half
#check @Zeta23.BL.rin_half
#check @Zeta23.BL.hwin_half_ge
#check @Zeta23.BL.log_half_ge
#check @Zeta23.BL.K_half_ge
#check @Zeta23.BL.rpow_neg_five_half_mul
#check @Zeta23.BL.log_three_nonneg
#check @Zeta23.BL.bohrLandau_explicit
#check @Zeta23.MNF_Ncount_le_mul_log
#check @Zeta23.MNF_mul_log_le_Ncount
#check @MNF.RH.abs_re_sub_half_lt_half
#check @MNF.RH.abs_re_sub_half_le_half
#check @MNF.RH.NOff_anti
#check @MNF.RH.NOff_antitone
#check @MNF.RH.NOff_intervalIntegrable
#check @MNF.RH.indicator_le_antitone
#check @MNF.RH.term_intervalIntegrable
#check @MNF.RH.integral_indicator_le_eq
#check @MNF.RH.reservoirMass_eq_integral
#check @MNF.RH.reservoirMass_nonneg
#check @MNF.RH.reservoirMass_le_half_Ncount
#check @MNF.RH.integral_NOff_split
#check @MNF.RH.integral_NOff_le_mul_Ncount
#check @MNF.RH.integral_NOff_tail_le
#check @MNF.RH.reservoirMass_le_split
#check @MNF.RH.reservoirMass_le_eps_Ncount
#check @MNF.RH.signedReservoir_eq_zero
#check @MNF.RH.sum_right_eq_sum_left
#check @MNF.RH.reservoirMass_eq_two_right
#check @MNF.RH.rpow_tail_intervalIntegrable
#check @MNF.RH.integral_rpow_tail_le
#check @MNF.RH.reservoirMass_le_rpow
#check @MNF.RH.reservoirMass_le_Ncount_mul
#check @MNF.RH.meanDisplacement_tendsto_zero
#check @Zeta23.Density.analyticOnNhd_Mx
#check @Zeta23.Density.analyticOnNhd_fz
#check @Zeta23.Density.continuousOn_fz
#check @Zeta23.Density.tail_inv_sq_le
#check @Zeta23.Density.fz_sub_one_eq
#check @Zeta23.Density.norm_fz_sub_one_le
#check @Zeta23.Density.pi_sq_lt_ten
#check @Zeta23.Density.pi_sq_div_six_div_le
#check @Zeta23.Density.norm_fz_le_one_add
#check @Zeta23.Density.one_sub_norm_le_norm_fz
#check @Zeta23.Density.fz_lower_two
#check @Zeta23.Density.neg_log_norm_fz_two_le
#check @Zeta23.Density.log_norm_fz_le_of_two_le_re
#check @Zeta23.Density.norm_sq_fz_le_of_two_le_re
#check @Zeta23.Density.abs_cm_le
#check @Zeta23.Density.cm_eq_of_le
#check @Zeta23.Density.S_mul_Mx_eq
#check @Zeta23.Density.card_filter_dvd_dvd_le
#check @Zeta23.Density.gcd_le_sum_dvd
#check @Zeta23.Density.gcd_le_sum_Icc
#check @Zeta23.Density.sum_div_of_dvd_le
#check @Zeta23.Density.ite_and_div_eq
#check @Zeta23.Density.sum_gcd_div_le
#check @Zeta23.Density.dX_eq_card_filter
#check @Zeta23.Density.dX_eq_sum
#check @Zeta23.Density.sum_dX_sq_le
#check @Zeta23.Density.sum_mul_le_of_partial_sums
#check @Zeta23.Density.sum_mul_le_of_partial_sums_tail
#check @Zeta23.Density.sum_Ioc_rpow_le
#check @Zeta23.Density.tail_sum_le
#check @Zeta23.Density.weight_sum_le
#check @Zeta23.Density.integral_window_eq
#check @Zeta23.Density.norm_coeff_sq
#check @Zeta23.Density.abs_cm_sq_le
#check @Zeta23.Density.meanSquare_prodPoly
#check @Zeta23.Density.norm_add_sq_le_eta
#check @Zeta23.Density.norm_Mx_le
#check @Zeta23.Density.continuousOn_B_window
#check @Zeta23.Density.integral_inv_sq_window
#check @Zeta23.Density.meanSquare_B_window
#check @Zeta23.Density.continuous_A_window
#check @Zeta23.Density.continuousOn_fz_window
#check @Zeta23.Density.meanSquare_fz_window
#check @Zeta23.Density.sum_Icc_two_inv_mul_sub_one
#check @Zeta23.Density.norm_moebius_mul_cpow_le
#check @Zeta23.Density.Mx_eq_one_add
#check @Zeta23.Density.Mx_ne_zero_of_le_re
#check @Zeta23.Density.analyticOrderAt_Mx_ne_top
#check @Zeta23.Density.zeta_order_le_divisor_fz
#check @Zeta23.Density.finset_sum_zeta_order_le_finsum_divisor_fz
#check @Zeta23.Density.fz_two_add_ne_zero
#check @Zeta23.Density.count_disc_le_fz
#check @Zeta23.Density.count_finset_le_fz
#check @Zeta23.Density.count_window_le_fz
#check @Zeta23.Density.log_norm_le_Leps
#check @Zeta23.Density.continuousOn_Leps
#check @Zeta23.Density.circleAverage_log_norm_le_Leps
#check @Zeta23.Density.concaveOn_half_log_add
#check @Zeta23.Density.half_log_le_half
#check @Zeta23.Density.segment_average_Leps_le
#check @Zeta23.Density.continuousOn_Leps_fz_ne_one
#check @Zeta23.Density.continuousOn_Leps_circleMap
#check @Zeta23.Density.integrableOn_Leps_circleMap_prod
#check @Zeta23.Density.integrable_Leps_circleMap_prod_restrict
#check @Zeta23.Density.intervalIntegrable_circleAverage_Leps
#check @Zeta23.Density.integral_circleAverage_Leps_eq_swap
#check @Zeta23.Density.intervalIntegrable_Leps_segment
#check @Zeta23.Density.intervalIntegrable_normSq_fz_segment
#check @Zeta23.Density.circleAverage_log_fz_le_Leps
#check @Zeta23.Density.count_le_integral_fz_window
#check @Zeta23.Density.count_le_integral_fz_NSigma
#check @Zeta23.Density.NRight_sub_eq_NSigma
#check @Zeta23.Density.count_le_integral_fz
#check @Zeta23.Density.integral_Leps_segment_le_of_meanSquare
#check @Zeta23.Density.Leps_fz_le_of_two_le_re
#check @Zeta23.Density.integral_Leps_segment_le_of_two_le
#check @Zeta23.Density.integral_Leps_circle_le
#check @Zeta23.Density.integral_circleAverage_Leps_le
#check @Zeta23.Density.count_le_meanSquare_fz_window
#check @Zeta23.Density.count_le_meanSquare_fz
#check @Zeta23.Density.theta_pos
#check @Zeta23.Density.theta_le_one
#check @Zeta23.Density.kappa_pos
#check @Zeta23.Density.kappa_le_theta
#check @Zeta23.Density.theta_mul_eq
#check @Zeta23.Density.offdiag_exponent
#check @Zeta23.Density.cross_exponent
#check @Zeta23.Density.cross_exponent'
#check @Zeta23.Density.half_le_nat_floor
#check @Zeta23.Density.rpow_sq_eq
#check @Zeta23.Density.two_rpow_le_two
#check @Zeta23.Density.one_add_log_cube_le_rpow
#check @Zeta23.Density.single_params
#check @Zeta23.Density.X_rpow_le
#check @Zeta23.Density.rpow_le_X_rpow
#check @Zeta23.Density.NX_rpow_div_le
#check @Zeta23.Density.inv_X_le
#check @Zeta23.Density.E0gen_le
#check @Zeta23.Density.le_E0gen
#check @Zeta23.Density.E0gen_le_const
#check @Zeta23.Density.cross_le
#check @Zeta23.Density.Egen_le
#check @Zeta23.Density.Ksingle_pos
#check @Zeta23.Density.exponent_single
#check @Zeta23.Density.w4_rhs_le
#check @Zeta23.Density.geom_lower
#check @Zeta23.Density.count_le_Egen
#check @Zeta23.Density.density_single_window
#check @MNF.RH.mirror_re
#check @MNF.RH.mirror_im
#check @MNF.RH.mirror_mirror
#check @MNF.RH.mirror_injective
#check @MNF.RH.is_nontrivial_zero_mirror
#check @MNF.RH.mirror_mem_zerosIn
#check @MNF.RH.zeta_order_mirror
#check @MNF.RH.is_nontrivial_zero_conj
#check @MNF.RH.mirror_eq_self_iff
#check @MNF.RH.one_le_zeta_order
#check @MNF.RH.inBand_or_inReservoir_or_onLine
#check @MNF.RH.inBand_mirror_iff
#check @MNF.RH.mem_bandZeros_mirror
#check @MNF.RH.degenerate_of_not_onLine
#check @MNF.RH.onLine_and_simple_of_not_degenerate
#check @MNF.RH.not_degenerate_of_onLine_simple
#check @MNF.RH.noDegenerate_iff
#check @MNF.RH.spectralGapHyp_iff_not_inBand
#check @MNF.RH.spectralGapHyp_iff_ordinatesInjectiveOn_bandZeros
#check @MNF.RH.bandCoincidentMass_eq_zero_of_spectralGapHyp
#check @MNF.RH.not_inBand_of_bandCoincidentMass_eq_zero
#check @MNF.RH.spectralGapHyp_iff_bandCoincidentMass_of_im_ne_zero
#check @MNF.RH.zeta_em_remainder_norm_le
#check @MNF.RH.riemannZeta_ofReal_ne_zero_of_mem_Ioo
#check @MNF.RH.nontrivial_zero_im_ne_zero
#check @MNF.RH.spectralGapHyp_iff_bandCoincidentMass
#check @MNF.RH.bandCoincidentMass_nonneg
#check @MNF.RH.bandCoincidentMass_le_offDiagonalCoincidentMass
#check @MNF.RH.finsum_mem_inter_setOf_eq_sum_filter
#check @MNF.RH.NOffLine_real_eq_sum_filter
#check @MNF.RH.N0_real_eq_sum_filter
#check @MNF.RH.Ncount_eq_N0_add_NOffLine
#check @MNF.RH.pairSum_eq_sum
#check @MNF.RH.pairSum_const
#check @MNF.RH.pairSum_fst
#check @MNF.RH.pairSum_snd
#check @MNF.RH.pairSum_fst_indicator
#check @MNF.RH.pairSum_fst_abs
#check @MNF.RH.pairSum_fst_abs_eq_integral
#check @MNF.RH.pairSum_swap
#check @MNF.RH.pairSum_nonneg
#check @MNF.RH.pairSum_mono
#check @MNF.RH.diagonalMass_nonneg
#check @MNF.RH.diagonalMass_le_sq_Ncount
#check @MNF.RH.Ncount_le_diagonalMass
#check @MNF.RH.coincidentMass_eq
#check @MNF.RH.offDiagonalCoincidentMass_nonneg
#check @MNF.RH.offLine_sq_le_offDiagonalCoincidentMass
#check @MNF.RH.offDiagonalCoincidentMass_le
#check @MNF.RH.offDiagonalCoincidentMass_le_two_mul
#check @MNF.RH.offDiagonalCoincidentMass_eq_zero_of_onLine
#check @MNF.RH.onLine_of_offDiagonalCoincidentMass_eq_zero
#check @MNF.RH.offDiagonalCoincidentMass_le_two_thirds
#check @MNF.RH.offDiagonalCoincidentMass_le_five_ninths
