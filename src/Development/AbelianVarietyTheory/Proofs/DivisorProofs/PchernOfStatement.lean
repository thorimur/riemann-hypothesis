import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PchernOf
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pChern_neg_one : GlobalTheory.AnPer.PChern (-1) := by
  first | exact @GlobalTheory.AnPer.ChernClause.pchern | exact GlobalTheory.AnPer.ChernClause.pchern | (intros; apply GlobalTheory.AnPer.ChernClause.pchern <;> assumption)
