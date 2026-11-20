import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntisymmetricDiscriminantInvariant
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.antisymmetric_discriminant_invariant : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (j : ℕ) (al be : ι → ℝ), AntiL j (delPol ι N * invForm j al be) ∧ (delPol ι N * invForm (N := N) j al be).IsHomogeneous (dimFl ι N + 1) := by
  first | exact @GlobalTheory.FlagPoly.DiscLin.delPol_mul_invForm | exact GlobalTheory.FlagPoly.DiscLin.delPol_mul_invForm | (intros; apply GlobalTheory.FlagPoly.DiscLin.delPol_mul_invForm <;> assumption)
