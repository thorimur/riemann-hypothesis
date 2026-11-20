import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homExtension_semiAbelian_discreteValuationRing : GlobalTheory.LN.HomExtSt := by
  first | exact @GlobalTheory.homExtension_semiAbelian_dvr | exact GlobalTheory.homExtension_semiAbelian_dvr | (intros; apply GlobalTheory.homExtension_semiAbelian_dvr <;> assumption)
