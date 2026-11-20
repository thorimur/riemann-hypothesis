import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePoints
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduliScheme_levelMaps_heckePoints' : N1 := by
  first | exact @GlobalTheory.moduliScheme_levelMaps_heckePoints | exact GlobalTheory.moduliScheme_levelMaps_heckePoints | (intros; apply GlobalTheory.moduliScheme_levelMaps_heckePoints <;> assumption)
