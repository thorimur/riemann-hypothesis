import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFullLevelAmpleModelOfSemistableReduction
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fullLevelAmpleModel_of_semistableReduction : GlobalTheory.Published.SemistableReductionSt → GlobalTheory.Models.TopAmpExists := by
  first | exact @GlobalTheory.topAmpExists_of_semistableReduction | exact GlobalTheory.topAmpExists_of_semistableReduction | (intros; apply GlobalTheory.topAmpExists_of_semistableReduction <;> assumption)
