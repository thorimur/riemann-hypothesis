import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftFunctionalLinearRootPower
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shift_functional_linear_root_power : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (j : ℕ) (u : ι → Fin N → ℝ) (τ : ι), shF j τ (linRoot u ^ (dimFl ι N + 1)) = -((dimFl ι N : ℝ) + 1) * flagDeg ι N u * ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), u τ i ∧ totF τ (linRoot u ^ (dimFl ι N + 1)) = -((dimFl ι N : ℝ) + 1) * flagDeg ι N u * ∑ i : Fin N, u τ i := by
  first | exact @GlobalTheory.FlagPoly.DerivPow.shF_totF_linRoot_pow | exact GlobalTheory.FlagPoly.DerivPow.shF_totF_linRoot_pow | (intros; apply GlobalTheory.FlagPoly.DerivPow.shF_totF_linRoot_pow <;> assumption)
