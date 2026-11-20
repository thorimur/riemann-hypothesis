import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ZarhinProjectiveModelOfSemistableReduction
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinProjectiveModel_of_semistableReduction : GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ZHSt := by
  first | exact @GlobalTheory.zh_of_semistableReduction | exact GlobalTheory.zh_of_semistableReduction | (intros; apply GlobalTheory.zh_of_semistableReduction <;> assumption)
