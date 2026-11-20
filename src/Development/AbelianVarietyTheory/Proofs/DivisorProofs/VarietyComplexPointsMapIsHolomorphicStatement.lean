import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VarietyComplexPointsMapIsHolomorphic
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.varietyComplexPointsMap_isHolomorphic : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), (atlas X σ).IsHolo (atlas Y σ) (ptMap σ f hf) := by
  first | exact @GlobalTheory.ChernCalc.ptMap_isHolo | exact GlobalTheory.ChernCalc.ptMap_isHolo | (intros; apply GlobalTheory.ChernCalc.ptMap_isHolo <;> assumption)
