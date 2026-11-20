import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NoetherianIntegralClosedCover
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noetherian_integral_closed_cover : ∀ (X : Scheme.{0}) [IsNoetherian X], ∃ (n : ℕ) (Z : Fin n → Scheme.{0}) (j : ∀ i, Z i ⟶ X), (∀ i, IsIntegral (Z i) ∧ IsClosedImmersion (j i)) ∧ ∀ x : X, ∃ i, x ∈ Set.range (j i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.exists_integral_closed_cover | exact GlobalTheory.CompanionTheory.Ar.Approx.exists_integral_closed_cover | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.exists_integral_closed_cover <;> assumption)
