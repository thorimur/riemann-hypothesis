import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommAlgFunctorCohomologyCupAnticomm
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commAlgFunctorCohomologyCup_anticomm : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (a b : GlobalTheory.CatCoh.H1 F), cup F a b = - cup F b a := by
  first | exact @GlobalTheory.AbCoh.cup_anticomm | exact GlobalTheory.AbCoh.cup_anticomm | (intros; apply GlobalTheory.AbCoh.cup_anticomm <;> assumption)
