import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FunctionalEquationAllDegreesAlgebraicClosure
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functional_equation_all_degrees_algebraic_closure : Laws → Laws2 → AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => D.TauBimult → U.FE (Kbar V) 1 → ∀ N : ℕ, 1 ≤ N → U.FE (Kbar V) N := by
  first | exact @GlobalTheory.UU.fe_all_degrees | exact GlobalTheory.UU.fe_all_degrees | (intros; apply GlobalTheory.UU.fe_all_degrees <;> assumption)
