import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMultiplicationPullbackGenericSectionCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multiplicationPullback_genericSection_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ θ₀ : SecK C.P.L.L C.α 1, ∃ S : SecK C.P.L.L C.α (m ^ 2), MulSecK C m θ₀ S := by
  first | exact @GlobalTheory.Mum.exists_mulSecK | exact GlobalTheory.Mum.exists_mulSecK | (intros; apply GlobalTheory.Mum.exists_mulSecK <;> assumption)
