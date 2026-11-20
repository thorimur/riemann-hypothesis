import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfFlatPointAtGenericPoints
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_of_flat_point_at_generic_points : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] (X : Scheme.{0}) (s : X ⟶ Sp R) (x : Sp K ⟶ X) (β : R →+* K), Flat s → Set.range x ⊆ genericPoints X → x ≫ s = spMap β → Function.Injective β := by
  first | exact @GlobalTheory.injective_of_flat_of_range_subset_genericPoints | exact GlobalTheory.injective_of_flat_of_range_subset_genericPoints | (intros; apply GlobalTheory.injective_of_flat_of_range_subset_genericPoints <;> assumption)
