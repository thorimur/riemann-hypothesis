import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasse_norm_theorem_quadratic_extension : GlobalTheory.Published.HasseNormSt := by
  first | exact @GlobalTheory.QNorm.hasseNormSt | exact GlobalTheory.QNorm.hasseNormSt | (intros; apply GlobalTheory.QNorm.hasseNormSt <;> assumption)
