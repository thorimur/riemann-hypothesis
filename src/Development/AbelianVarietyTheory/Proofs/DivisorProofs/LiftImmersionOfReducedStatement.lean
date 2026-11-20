import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftImmersionOfReduced
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_of_isReduced_of_isImmersion_range : ∀ (X Y P : Scheme.{0}) (f : X ⟶ P) (j : Y ⟶ P), IsReduced X → IsImmersion j → Set.range f ⊆ Set.range j → ∃ g : X ⟶ Y, g ≫ j = f := by
  first | exact @GlobalTheory.Mum.lift_immersion_of_reduced | exact GlobalTheory.Mum.lift_immersion_of_reduced | (intros; apply GlobalTheory.Mum.lift_immersion_of_reduced <;> assumption)
