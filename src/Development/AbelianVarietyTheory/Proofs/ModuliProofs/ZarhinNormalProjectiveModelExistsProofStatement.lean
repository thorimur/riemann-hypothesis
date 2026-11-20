import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ZarhinNormalProjectiveModelExistsProof
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinNormalProjectiveModelExists_proof : GlobalTheory.ZH.ZHSt := by
  first | exact @GlobalTheory.zhSt_holds | exact GlobalTheory.zhSt_holds | (intros; apply GlobalTheory.zhSt_holds <;> assumption)
