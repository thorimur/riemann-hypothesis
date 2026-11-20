import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusHomEqOneOfNoCocharacter
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitTorus_hom_eq_one_of_no_cocharacter' : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X], (∀ f : Gm S ⟶ B, IsMonHom f → f = 1) → ∀ u : splitTorus S X ⟶ B, IsMonHom u → u = 1 := by
  first | exact @GlobalTheory.SS.splitTorus_hom_eq_one_of_no_cocharacter | exact GlobalTheory.SS.splitTorus_hom_eq_one_of_no_cocharacter | (intros; apply GlobalTheory.SS.splitTorus_hom_eq_one_of_no_cocharacter <;> assumption)
