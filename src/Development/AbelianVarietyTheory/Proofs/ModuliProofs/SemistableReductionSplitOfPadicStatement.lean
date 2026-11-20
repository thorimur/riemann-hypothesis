import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SemistableReductionSplitOfPadic
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistableReductionSplit_of_padic : GlobalTheory.Published.SemistableReductionSt → GlobalTheory.SS.SemistablePol := by
  first | exact @GlobalTheory.SS.semistablePol_of_padic | exact GlobalTheory.SS.semistablePol_of_padic | (intros; apply GlobalTheory.SS.semistablePol_of_padic <;> assumption)
