import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapBijectiveOfIsIsoRestrict
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functionFieldMap_bijective_of_isIso_restrict' : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] (U : X.Opens), (U : Set X).Nonempty → IsIso (s ∣_ U) → Function.Bijective (functionFieldMap s) := by
  first | exact @GlobalTheory.Discrepancy.functionFieldMap_bijective_of_isIso_restrict | exact GlobalTheory.Discrepancy.functionFieldMap_bijective_of_isIso_restrict | (intros; apply GlobalTheory.Discrepancy.functionFieldMap_bijective_of_isIso_restrict <;> assumption)
