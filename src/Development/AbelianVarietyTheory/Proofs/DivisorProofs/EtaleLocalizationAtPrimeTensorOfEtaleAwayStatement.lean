import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeTensorOfEtaleAway
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_localization_atPrime_tensor_of_etale_away' : ∀ (R C : Type) [CommRing R] [CommRing C] [Algebra R C] (b : R),
    Algebra.Etale R (Localization.Away (algebraMap R C b)) →
    ∀ (P : Ideal R) [P.IsPrime], b ∉ P →
      Algebra.Etale (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P) C) := by
  first | (exact @GlobalTheory.etale_localization_atPrime_tensor_of_etale_away) | (exact GlobalTheory.etale_localization_atPrime_tensor_of_etale_away) | (intros; apply GlobalTheory.etale_localization_atPrime_tensor_of_etale_away <;> assumption)
