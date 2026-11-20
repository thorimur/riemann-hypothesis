import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionEqOfLaws
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_torsion_eq_of_laws : Laws → Laws2 → Laws3 → Laws4 → Laws5 → GlobalTheory.ZH.UTorsSt := by
  first | exact @GlobalTheory.ZH.uTors_of_laws | exact GlobalTheory.ZH.uTors_of_laws | (intros; apply GlobalTheory.ZH.uTors_of_laws <;> assumption)
