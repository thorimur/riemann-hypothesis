import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftToCompleteDvrOfFinite
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_to_complete_dvr_of_finite' : ∀ (A R : Type) [CommRing A] [CommRing R] [Algebra A R], Function.Injective (algebraMap A R) →
    Module.Finite A R → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (maximalIdeal V) V → ∀ h : A →+* V,
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : CharZero V')
      (f : V →+* V') (ρ : R →+* V'), IsAdicComplete (maximalIdeal V') V' ∧
      Function.Injective f ∧ IsLocalHom f ∧ ρ.comp (algebraMap A R) = f.comp h := by
  first | exact @GlobalTheory.exists_lift_to_complete_dvr_of_finite | exact GlobalTheory.exists_lift_to_complete_dvr_of_finite | (intros; apply GlobalTheory.exists_lift_to_complete_dvr_of_finite <;> assumption)
