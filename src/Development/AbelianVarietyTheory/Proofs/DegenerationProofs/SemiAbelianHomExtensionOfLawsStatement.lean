import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemiAbelianHomExtensionOfLaws
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelianHomExtension_of_laws : Laws → Laws2 → HomExtSt := by
  first | exact @GlobalTheory.LN.homExt_of_laws | exact GlobalTheory.LN.homExt_of_laws | (intros; apply GlobalTheory.LN.homExt_of_laws <;> assumption)
