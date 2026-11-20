import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAtLcAtOfLeCoeff
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kltAt_and_lcAt_antitone_coeff : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Γ B : X → ℚ) (a b : ℚ) (x : X), IsQCart B → a ≤ b → (KltAt p n (Γ + b • B) x → KltAt p n (Γ + a • B) x) ∧ (LcAt p n (Γ + b • B) x → LcAt p n (Γ + a • B) x) := by
  first | exact @GlobalTheory.PairStep.kltAt_lcAt_of_le_coeff | exact GlobalTheory.PairStep.kltAt_lcAt_of_le_coeff | (intros; apply GlobalTheory.PairStep.kltAt_lcAt_of_le_coeff <;> assumption)
