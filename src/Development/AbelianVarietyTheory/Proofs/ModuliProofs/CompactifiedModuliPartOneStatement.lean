import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOne
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactifiedModuli_partOne : PartI := by
  first | exact @GlobalTheory.partI_closed | exact GlobalTheory.partI_closed | (intros; apply GlobalTheory.partI_closed <;> assumption)
