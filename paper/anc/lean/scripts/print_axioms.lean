import PositivityRigidityII
/-! `#print axioms` for the headline theorems of Part II and for every other formalised statement.  Output:
`axioms.log` (`lake env lean scripts/print_axioms.lean`, with the `# ` header of `axioms.log`); `scripts/audit.sh`
requires the output to equal `axioms.log`, its `# ` header lines excepted, exactly. -/
-- Theorem S (thm:main-S)
#print axioms PosRigII.theorem1
#print axioms PosRigII.theorem1_conductor
#print axioms PosRigII.theorem1_finite
#print axioms PosRigII.theorem1_object
-- Theorem U (thm:main-U)
#print axioms PosRigII.theorem2
#print axioms PosRigII.theorem2_condU
-- Corollary (cor:main-RH)
#print axioms PosRigII.corollary3
#print axioms PosRigII.corollary3_RH
#print axioms PosRigII.corollary3_notRH
#print axioms PosRigII.corollary_minimiser
#print axioms PosRigII.main_summary
-- Section "Reduction" (sec:reduction): Lemma lem:voronoi (a), Proposition prop:reduction, and its steps
#print axioms PosRigII.classW_inTδ
#print axioms PosRigII.classW_mem_TestClass
#print axioms PosRigII.reduction
#print axioms PosRigII.reduction_OPS
#print axioms PosRigII.condC5_of
#print axioms PosRigII.FT_nonneg_of_voronoi
#print axioms PosRigII.FT_xiOf_eq_zero_of_voronoi
#print axioms PosRigII.FT_zero_of_voronoi
#print axioms PosRigII.Arch_eq_zero_of_FT_vanish
#print axioms PosRigII.intR_pos_of_C2
-- The object (sec:assembly): normalisation and the exact magic function
#print axioms PosRigII.exists_object
#print axioms PosRigII.ZF_Xi_sq_mul
-- Faithfulness and sanity (no ledger axiom)
#print axioms PosRigII.gammaInf_eq_gammaR
#print axioms PosRigII.gammaInf_zero
#print axioms PosRigII.Xi_eq_gammaInf_mul_zeta
#print axioms PosRigII.one_classW
#print axioms PosRigII.ClassW.smul
#print axioms PosRigII.GammaFT_smul
#print axioms PosRigII.ClassW.exists_real_ne_zero
#print axioms PosRigII.voronoiTerm_zero
#print axioms PosRigII.voronoiTerm_one
#print axioms PosRigII.xiOf_add_natCast
#print axioms PosRigII.hasDerivAt_eq_zero_of_nonneg
-- Corollary 8.2 (cor:nogap, "The classical cone") and Lemma C.1 (lem:transfer), Appendix C
#print axioms PosRigII.rh_iff_kappaOPS_zero
#print axioms PosRigII.corollary8_2
#print axioms PosRigII.corollary8_2_b
#print axioms PosRigII.FT_window
#print axioms PosRigII.kappaStar_nonneg_iff_kappaOPS_nonneg
#print axioms PosRigII.arch_nonneg_Cone_iff_ConeOPS
#print axioms PosRigII.transfer
#print axioms PosRigII.transfer_Arch
#print axioms PosRigII.Arch_add
#print axioms PosRigII.TestClass.add
#print axioms PosRigII.TestClass.integrable_re_mul_Ωinf
#print axioms PosRigII.ConeG_zero_eq
#print axioms PosRigII.slack_anti
#print axioms PosRigII.FT_re_ge_GammaFT_re
