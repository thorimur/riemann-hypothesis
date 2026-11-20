import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFunctionalEquationSectionNonzeroClass
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_functionalEquation_section_nonzero_class : Laws → Laws2 → AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => D.TauBimult → ∀ k : ℕ, 1 ≤ k → U.FE (Kbar V) 1 → U.FE (Kbar V) k → (∃ β, U.Supp (Kbar V) 1 β) → (∃ β, U.Supp (Kbar V) k β) → ∀ α, ∃ t s, U.ExpF (Kbar V) (k + 1) t s ∧ DegPre.FamFE D (Kbar V) (k + 1) s ∧ ∃ j, (s α).f j ≠ 0 := by
  first | exact @GlobalTheory.UU.FESection.main | exact GlobalTheory.UU.FESection.main | (intros; apply GlobalTheory.UU.FESection.main <;> assumption)
