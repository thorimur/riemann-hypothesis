import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonzeroOnClosedFibreCompleteLocal
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_nonzero_on_closed_fibre_complete_local : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsNoetherianRing R → IsIntegrallyClosed R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → CharZero R → ∀ (D : DegData R (IsLocalRing.maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal R) D A G), ∃ θ : LB.Sec U.LG.L, ∃ x ∈ nonzeroLocus θ, G.hom x = IsLocalRing.closedPoint R := by
  first | exact @GlobalTheory.ThetaClosed.exists_section_nonzero_closed | exact GlobalTheory.ThetaClosed.exists_section_nonzero_closed | (intros; apply GlobalTheory.ThetaClosed.exists_section_nonzero_closed <;> assumption)
