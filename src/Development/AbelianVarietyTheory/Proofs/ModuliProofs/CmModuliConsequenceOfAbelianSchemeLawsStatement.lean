import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmModuli_consequence_of_abelianSchemeLaws : N1c := by
  first | exact @GlobalTheory.closing_of_abelianSchemeLaws | exact GlobalTheory.closing_of_abelianSchemeLaws | (intros; apply GlobalTheory.closing_of_abelianSchemeLaws <;> assumption)
