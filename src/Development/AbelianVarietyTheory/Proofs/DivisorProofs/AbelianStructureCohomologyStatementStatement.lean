import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianStructureCohomologyStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_structure_cohomology_statement : GlobalTheory.AbCoh.OStr := by
  first | exact @GlobalTheory.AbCoh.oStr | exact GlobalTheory.AbCoh.oStr | (intros; apply GlobalTheory.AbCoh.oStr <;> assumption)
