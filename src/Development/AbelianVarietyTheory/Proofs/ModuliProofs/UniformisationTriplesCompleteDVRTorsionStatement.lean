import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationTriplesCompleteDVRTorsion
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_triples_complete_DVR_torsion : GlobalTheory.LN.UDvrSt := by
  first | exact @GlobalTheory.LN.uDvrSt_holds | exact GlobalTheory.LN.uDvrSt_holds | (intros; apply GlobalTheory.LN.uDvrSt_holds <;> assumption)
