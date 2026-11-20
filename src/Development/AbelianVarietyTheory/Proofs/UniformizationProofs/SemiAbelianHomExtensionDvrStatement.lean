import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvr
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_hom_extension_dvr : HomExtSt := by
  first | exact @GlobalTheory.homExtension_semiAbelian_dvr_unconditional | exact GlobalTheory.homExtension_semiAbelian_dvr_unconditional | (intros; apply GlobalTheory.homExtension_semiAbelian_dvr_unconditional <;> assumption)
