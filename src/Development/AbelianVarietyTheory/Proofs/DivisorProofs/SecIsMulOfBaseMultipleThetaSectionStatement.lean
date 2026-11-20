import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecIsMulOfBaseMultipleThetaSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secIsMul_of_baseMultiple_thetaSection : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (th g : GlobalTheory.UU.SecBT D (𝟙_ _) 1 0) (b : R), GlobalTheory.PsiRing.Mult D th g b → ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom b g th := by
  first | exact @GlobalTheory.PsiRing.secIsMul_of_mult | exact GlobalTheory.PsiRing.secIsMul_of_mult | (intros; apply GlobalTheory.PsiRing.secIsMul_of_mult <;> assumption)
