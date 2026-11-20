import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSquareGlobalOneFormEqZeroOfAxesStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

theorem GlobalTheory.AbCoh.primF_of_isAbelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.PrimF A :=
  fun R _ A _ g hA hg ↦ GlobalTheory.AbCoh.PrimForm.prim_of_axes A (GlobalTheory.T.abelianSquare_globalOneForm_eq_zero_of_axes R A g hA hg)
