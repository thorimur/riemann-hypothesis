import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformization_laws_and_expansion_statements : GlobalTheory.UT.LL ∧ DVR.TwistBCSpanStatement ∧ DVR.TWM.VRatioGtStatement ∧ DVR.TWStatement ∧ DVR.UUStatement := by
  first | exact @GlobalTheory.lawsAndExpansions | exact GlobalTheory.lawsAndExpansions | (intros; apply GlobalTheory.lawsAndExpansions <;> assumption)
