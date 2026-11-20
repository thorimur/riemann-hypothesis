import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaExpansionFunctionalEquationDegreeOne
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaExpansion_functionalEquation_degree_one : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → PsiRel D (𝟙_ _) f → U.FE (Kbar V) 1) := by
  first | exact @GlobalTheory.UU.fe_one_of_psiRel | exact GlobalTheory.UU.fe_one_of_psiRel | (intros; apply GlobalTheory.UU.fe_one_of_psiRel <;> assumption)
