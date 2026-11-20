import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricPointDvrFactorsValuationSubringClosure
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_point_dvr_factors_valuation_subring_closure : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp W), ∃ (U : ValuationSubring (AlgebraicClosure L)) (j : W →+* U) (h : U →+* k), (algebraMap U (AlgebraicClosure L)).comp j = (algebraMap L (AlgebraicClosure L)).comp (algebraMap W L) ∧ x = spMap h ≫ spMap j := by
  first | exact @GlobalTheory.geomPoint_factors_valuationSubring_algClosure | exact GlobalTheory.geomPoint_factors_valuationSubring_algClosure | (intros; apply GlobalTheory.geomPoint_factors_valuationSubring_algClosure <;> assumption)
