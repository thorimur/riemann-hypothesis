import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ZarhinGeometricOfSemistableReduction
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinGeometric_of_semistableReduction : GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ZHGeoSt := by
  first | exact @GlobalTheory.zhGeo_of_semistableReduction | exact GlobalTheory.zhGeo_of_semistableReduction | (intros; apply GlobalTheory.zhGeo_of_semistableReduction <;> assumption)
