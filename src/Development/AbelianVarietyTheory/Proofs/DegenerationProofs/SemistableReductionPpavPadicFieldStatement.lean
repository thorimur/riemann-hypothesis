import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableReductionPpavPadicField
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistableReduction_ppav_padicField : GlobalTheory.Published.SemistableReductionSt := by
  first | exact @GlobalTheory.SS.semistableReductionSt | exact GlobalTheory.SS.semistableReductionSt | (intros; apply GlobalTheory.SS.semistableReductionSt <;> assumption)
