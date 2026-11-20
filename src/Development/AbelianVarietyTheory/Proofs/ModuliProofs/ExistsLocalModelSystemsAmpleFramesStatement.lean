import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalModelSystemsAmpleFrames
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localModelSystems_ampleFrames : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → Out.Laws3 → TopAmpExists → N1 → GlobalTheory.LN.ModelsSt := by
  first | exact @GlobalTheory.Models.exists_localSystems_ample | exact GlobalTheory.Models.exists_localSystems_ample | (intros; apply GlobalTheory.Models.exists_localSystems_ample <;> assumption)
