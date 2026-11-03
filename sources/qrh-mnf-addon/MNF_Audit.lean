/- Audit of the MNF.RH library: axiom reports and printed statements for every theorem the
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
#print axioms MNF.RH.zeroFree_seven_eighths
#print axioms MNF.RH.nontrivial_zero_re_le_seven_eighths
#print axioms MNF.RH.shifted_bounded_three_eighths
#print axioms MNF.RH.riemannHypothesis_iff_gap_three_eighths
#print axioms MNF.RH.riemannHypothesis_iff_remaining_strip_seven_eighths
#print axioms MNF.RH.rh_of_gap_three_eighths

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
#check MNF.RH.zeroFree_seven_eighths
#check MNF.RH.nontrivial_zero_re_le_seven_eighths
#check MNF.RH.shifted_bounded_three_eighths
#check MNF.RH.riemannHypothesis_iff_gap_three_eighths
#check MNF.RH.riemannHypothesis_iff_remaining_strip_seven_eighths
#check MNF.RH.rh_of_gap_three_eighths
