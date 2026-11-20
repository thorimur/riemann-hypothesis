import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamiliesExist
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelFamilies_exist : N0 := by
  first | exact @GlobalTheory.Moduli.siegelFamilies_closed | exact GlobalTheory.Moduli.siegelFamilies_closed | (intros; apply GlobalTheory.Moduli.siegelFamilies_closed <;> assumption)
