import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationCompleteDVR
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_completeDVR : GlobalTheory.LN.USt := by
  first | exact @GlobalTheory.uniformisation_dvr_unconditional | exact GlobalTheory.uniformisation_dvr_unconditional | (intros; apply GlobalTheory.uniformisation_dvr_unconditional <;> assumption)
