import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisLineBundleSectionsProjectiveOverDvr
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_lineBundleSections_projective_over_dvr : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of W)) (M : LB X), Flat f → GlobalTheory.AbLaw.IsProjBy f → M.IsLB → ∃ (n : ℕ) (t : Fin n → LB.Sec M), ∀ u : LB.Sec M, ∃! c : Fin n → W, u = ∑ j, GlobalTheory.AbLaw.cst f ⊤ (c j) • t j := by
  first | exact @GlobalTheory.AbLaw.exists_basis_sec_of_isDiscreteValuationRing | exact GlobalTheory.AbLaw.exists_basis_sec_of_isDiscreteValuationRing | (intros; apply GlobalTheory.AbLaw.exists_basis_sec_of_isDiscreteValuationRing <;> assumption)
