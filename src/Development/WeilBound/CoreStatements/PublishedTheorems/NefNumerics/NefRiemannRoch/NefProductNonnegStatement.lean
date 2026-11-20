import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefProductNonneg
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
theorem _root_.GlobalTheory.T.nef_product_nonneg : GlobalTheory.Published.NefProductNonneg := by
  first | exact @_root_.GlobalTheory.nefProductNonneg | exact _root_.GlobalTheory.nefProductNonneg | (intros; apply _root_.GlobalTheory.nefProductNonneg <;> assumption)
