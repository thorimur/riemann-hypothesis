import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimLeOfIsClosedNeUnivIntegral
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topologicalKrullDim_le_of_isClosed_ne_univ_integral : ∀ (X : Scheme.{0}) [IsIntegral X] (d : ℕ), topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ Z : Set X, IsClosed Z → Z ≠ Set.univ → topologicalKrullDim Z ≤ (d : ℕ) := by
  first | exact @GlobalTheory.topologicalKrullDim_le_of_isClosed_ne_univ | exact GlobalTheory.topologicalKrullDim_le_of_isClosed_ne_univ | (intros; apply GlobalTheory.topologicalKrullDim_le_of_isClosed_ne_univ <;> assumption)
