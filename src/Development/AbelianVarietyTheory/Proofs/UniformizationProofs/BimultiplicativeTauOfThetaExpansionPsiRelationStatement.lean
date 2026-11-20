import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BimultiplicativeTauOfThetaExpansionPsiRelation
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bimultiplicative_tau_of_thetaExpansionPsiRelation : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → PsiRel D (𝟙_ _) f → D.TauBimult) := by
  first | exact @GlobalTheory.tauBimult_of_psiRel | exact GlobalTheory.tauBimult_of_psiRel | (intros; apply GlobalTheory.tauBimult_of_psiRel <;> assumption)
