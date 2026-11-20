import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalOneFormsPrimitiveAbelianScheme
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalOneForms_primitive_abelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.PrimF A := by
  first | exact @GlobalTheory.AbCoh.primF_of_isAbelianScheme | exact GlobalTheory.AbCoh.primF_of_isAbelianScheme | (intros; apply GlobalTheory.AbCoh.primF_of_isAbelianScheme <;> assumption)
