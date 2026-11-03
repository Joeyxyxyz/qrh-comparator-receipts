/- Audit of the MNF.RH library (v3): axiom reports and printed statements for every theorem the
   Comparator challenge names. Compiled by scripts/mnf_report.sh with plain `lean`, sandboxed,
   against the tree Comparator built. -/
import MNF.RH.Unconditional

#print axioms MNF.RH.zeta_order_ge_one
#print axioms MNF.RH.order_one_iff_deriv
#print axioms MNF.RH.deriv_zero_of_high_order
#print axioms MNF.RH.allZerosSimple_iff_derivativeNonvanishing
#print axioms MNF.RH.nontrivial_zero_reflect
#print axioms MNF.RH.deriv_reflect
#print axioms MNF.RH.deriv_ne_zero_reflect_iff
#print axioms MNF.RH.analyticOrderAt_reflect
#print axioms MNF.RH.zeta_order_reflect
#print axioms MNF.RH.shifted_symmetric
#print axioms MNF.RH.in_strip_of_zero
#print axioms MNF.RH.riemannHypothesis_iff_strip
#print axioms MNF.RH.riemannHypothesis_iff_shifted_subset_zero
#print axioms MNF.RH.shifted_bounded
#print axioms MNF.RH.tau_threshold
#print axioms MNF.RH.riemannHypothesis_iff_gap_half
#print axioms MNF.RH.shifted_bounded_of_zeroFree
#print axioms MNF.RH.riemannHypothesis_iff_gap_of_zeroFree
#print axioms MNF.RH.riemannHypothesis_iff_remaining_strip
#print axioms MNF.RH.gap_below_bound_insufficient
#print axioms MNF.RH.symmetric_bounded_not_on_line
#print axioms MNF.RH.sign_gate_trivial
#print axioms MNF.RH.sign_gate_shifted
#print axioms MNF.RH.nullify_dilation
#print axioms MNF.RH.gap_iff_nullify_id
#print axioms MNF.RH.delta_from_ratio_38_insufficient
#print axioms MNF.RH.rh_of_gap
#print axioms MNF.RH.rh_of_gap_of_zeroFree
#print axioms MNF.RH.gap_of_rh
#print axioms MNF.RH.multiplicityBoundOne_iff_allZerosSimple
#print axioms MNF.RH.derivativeNonvanishing_of_left
#print axioms MNF.RH.allZerosSimple_of_speiser_and_double_zero_hyp
#print axioms MNF.RH.allZerosSimple_of_rh_of_line
#print axioms MNF.RH.rh_of_symmetric_operator
#print axioms MNF.RH.spectralGapHyp_iff_zeroFree_strip
#print axioms MNF.RH.spectralGapHyp_three_eighths_iff_of
#print axioms MNF.RH.zeroFree_seven_eighths
#print axioms MNF.RH.nontrivial_zero_re_le_seven_eighths
#print axioms MNF.RH.shifted_bounded_three_eighths
#print axioms MNF.RH.riemannHypothesis_iff_gap_three_eighths
#print axioms MNF.RH.riemannHypothesis_iff_remaining_strip_seven_eighths
#print axioms MNF.RH.rh_of_gap_three_eighths
#print axioms MNF.RH.spectralGapHyp_three_eighths_iff
#print axioms MNF.RH.rh_of_band_seven_eighths
#print axioms MNF.RH.mem_zerosIn
#print axioms MNF.RH.zerosIn_subset_zetaZeros
#print axioms MNF.RH.zerosIn_mono
#print axioms MNF.RH.zerosIn_subset_box
#print axioms MNF.RH.zerosIn_finite
#print axioms MNF.RH.Ncount_eq_sum
#print axioms MNF.RH.Ndist_eq_sum_ones
#print axioms MNF.RH.Ndist_le_Ncount
#print axioms MNF.RH.N0star_le_Ndist
#print axioms MNF.RH.N0simple_le_N0star
#print axioms MNF.RH.riemannHypothesis_iff_window_counts
#print axioms MNF.RH.allZerosSimple_iff_window_counts
#print axioms MNF.RH.N0simple_eq_deriv_form
#print axioms MNF.RH.gap_iff_zeroFreeBand
#print axioms MNF.RH.gap_of_right_side
#print axioms MNF.RH.rh_of_band_of_zeroFree
#print axioms MNF.RH.multipleZeroKillsGap_iff
#print axioms MNF.RH.fischerForward_iff
#print axioms MNF.RH.re_eq_half_of_real_eigenvalue
#print axioms MNF.RH.rh_of_realSpectrumRealization
#print axioms MNF.RH.allZerosSimple_of_multiplicity_dictionary
#print axioms MNF.RH.gap_of_mechanism
#print axioms MNF.RH.mechanism_of_gap
#print axioms MNF.RH.gapMechanism_iff
#print axioms MNF.RH.probe_balance
#print axioms MNF.RH.probe_reflect
#print axioms MNF.RH.probes_zero_iff
#print axioms wronskian_constant_same_eigenvalue
#print axioms wronskian_zero_of_l2
#print axioms linearly_dependent_of_wronskian_zero
#print axioms sturm_liouville_simple_eigenvalues
#print axioms MNF.RH.realization_forces_line
#print axioms MNF.RH.rh_of_realization
#print axioms MNF.RH.realSpectrumRealization_of_realization
#print axioms MNF.RH.eigenvalue_simple_of_realization
#print axioms MNF.RH.eigenfunction_unique_of_realization
#print axioms MNF.RH.allZerosSimple_of_realization
#print axioms MNF.RH.derivativeNonvanishing_of_realization
#print axioms MNF.RH.multiplicityDictionary_iff
#print axioms MNF.RH.N0_le_Ncount
#print axioms MNF.RH.NOff_le_Ncount
#print axioms MNF.RH.gap_forces_NOff_eq
#print axioms MNF.RH.on_line_density_one_of_gap

#check MNF.RH.zeta_order_ge_one
#check MNF.RH.order_one_iff_deriv
#check MNF.RH.deriv_zero_of_high_order
#check MNF.RH.allZerosSimple_iff_derivativeNonvanishing
#check MNF.RH.nontrivial_zero_reflect
#check MNF.RH.deriv_reflect
#check MNF.RH.deriv_ne_zero_reflect_iff
#check MNF.RH.analyticOrderAt_reflect
#check MNF.RH.zeta_order_reflect
#check MNF.RH.shifted_symmetric
#check MNF.RH.in_strip_of_zero
#check MNF.RH.riemannHypothesis_iff_strip
#check MNF.RH.riemannHypothesis_iff_shifted_subset_zero
#check MNF.RH.shifted_bounded
#check MNF.RH.tau_threshold
#check MNF.RH.riemannHypothesis_iff_gap_half
#check MNF.RH.shifted_bounded_of_zeroFree
#check MNF.RH.riemannHypothesis_iff_gap_of_zeroFree
#check MNF.RH.riemannHypothesis_iff_remaining_strip
#check MNF.RH.gap_below_bound_insufficient
#check MNF.RH.symmetric_bounded_not_on_line
#check MNF.RH.sign_gate_trivial
#check MNF.RH.sign_gate_shifted
#check MNF.RH.nullify_dilation
#check MNF.RH.gap_iff_nullify_id
#check MNF.RH.delta_from_ratio_38_insufficient
#check MNF.RH.rh_of_gap
#check MNF.RH.rh_of_gap_of_zeroFree
#check MNF.RH.gap_of_rh
#check MNF.RH.multiplicityBoundOne_iff_allZerosSimple
#check MNF.RH.derivativeNonvanishing_of_left
#check MNF.RH.allZerosSimple_of_speiser_and_double_zero_hyp
#check MNF.RH.allZerosSimple_of_rh_of_line
#check MNF.RH.rh_of_symmetric_operator
#check MNF.RH.spectralGapHyp_iff_zeroFree_strip
#check MNF.RH.spectralGapHyp_three_eighths_iff_of
#check MNF.RH.zeroFree_seven_eighths
#check MNF.RH.nontrivial_zero_re_le_seven_eighths
#check MNF.RH.shifted_bounded_three_eighths
#check MNF.RH.riemannHypothesis_iff_gap_three_eighths
#check MNF.RH.riemannHypothesis_iff_remaining_strip_seven_eighths
#check MNF.RH.rh_of_gap_three_eighths
#check MNF.RH.spectralGapHyp_three_eighths_iff
#check MNF.RH.rh_of_band_seven_eighths
#check MNF.RH.mem_zerosIn
#check MNF.RH.zerosIn_subset_zetaZeros
#check MNF.RH.zerosIn_mono
#check MNF.RH.zerosIn_subset_box
#check MNF.RH.zerosIn_finite
#check MNF.RH.Ncount_eq_sum
#check MNF.RH.Ndist_eq_sum_ones
#check MNF.RH.Ndist_le_Ncount
#check MNF.RH.N0star_le_Ndist
#check MNF.RH.N0simple_le_N0star
#check MNF.RH.riemannHypothesis_iff_window_counts
#check MNF.RH.allZerosSimple_iff_window_counts
#check MNF.RH.N0simple_eq_deriv_form
#check MNF.RH.gap_iff_zeroFreeBand
#check MNF.RH.gap_of_right_side
#check MNF.RH.rh_of_band_of_zeroFree
#check MNF.RH.multipleZeroKillsGap_iff
#check MNF.RH.fischerForward_iff
#check MNF.RH.re_eq_half_of_real_eigenvalue
#check MNF.RH.rh_of_realSpectrumRealization
#check MNF.RH.allZerosSimple_of_multiplicity_dictionary
#check MNF.RH.gap_of_mechanism
#check MNF.RH.mechanism_of_gap
#check MNF.RH.gapMechanism_iff
#check MNF.RH.probe_balance
#check MNF.RH.probe_reflect
#check MNF.RH.probes_zero_iff
#check wronskian_constant_same_eigenvalue
#check wronskian_zero_of_l2
#check linearly_dependent_of_wronskian_zero
#check sturm_liouville_simple_eigenvalues
#check MNF.RH.realization_forces_line
#check MNF.RH.rh_of_realization
#check MNF.RH.realSpectrumRealization_of_realization
#check MNF.RH.eigenvalue_simple_of_realization
#check MNF.RH.eigenfunction_unique_of_realization
#check MNF.RH.allZerosSimple_of_realization
#check MNF.RH.derivativeNonvanishing_of_realization
#check MNF.RH.multiplicityDictionary_iff
#check MNF.RH.N0_le_Ncount
#check MNF.RH.NOff_le_Ncount
#check MNF.RH.gap_forces_NOff_eq
#check MNF.RH.on_line_density_one_of_gap
