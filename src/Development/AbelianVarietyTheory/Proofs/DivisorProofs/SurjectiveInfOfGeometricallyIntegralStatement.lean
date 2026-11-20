import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveInfOfGeometricallyIntegral
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_inf_comp_of_geometricallyIntegral : ∀ (Z T : Scheme.{0}) (f : Z ⟶ T) [GeometricallyIntegral f] (O O' : Z.Opens), Surjective (O.ι ≫ f) → Surjective (O'.ι ≫ f) → Surjective ((O ⊓ O').ι ≫ f) := by
  first | exact @GlobalTheory.surjective_inf_of_geometricallyIntegral | exact GlobalTheory.surjective_inf_of_geometricallyIntegral | (intros; apply GlobalTheory.surjective_inf_of_geometricallyIntegral <;> assumption)
