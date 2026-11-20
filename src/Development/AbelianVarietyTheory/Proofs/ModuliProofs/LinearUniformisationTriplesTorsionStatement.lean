import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTriplesTorsion
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearUniformisation_triples_torsion : GlobalTheory.LN.PelSt := by
  first | exact @GlobalTheory.LN.pelSt_holds | exact GlobalTheory.LN.pelSt_holds | (intros; apply GlobalTheory.LN.pelSt_holds <;> assumption)
