import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EgaBundleFromLaws
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extension_of_abelian_schemes : Laws → Laws2 → Ega := by
  first | exact @GlobalTheory.LN.ega_of_laws | exact GlobalTheory.LN.ega_of_laws | (intros; apply GlobalTheory.LN.ega_of_laws <;> assumption)
