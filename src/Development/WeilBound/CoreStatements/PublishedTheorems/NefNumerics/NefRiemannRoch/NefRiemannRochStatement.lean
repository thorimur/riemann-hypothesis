import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefRiemannRoch
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
theorem _root_.GlobalTheory.T.nef_riemann_roch : GlobalTheory.Published.NefRiemannRoch := by
  first | exact @_root_.GlobalTheory.nefRiemannRoch | exact _root_.GlobalTheory.nefRiemannRoch | (intros; apply _root_.GlobalTheory.nefRiemannRoch <;> assumption)
