import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderTranslationInvariant
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hopf_order_translation_invariant : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (A : Subalgebra R (T → R)), IsHopfOrder A → ∀ f ∈ A, ∀ t, (fun h => f (t * h)) ∈ A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.HopfTranslate.translate_mem_of_isHopfOrder | exact GlobalTheory.CompanionTheory.Ar.BT.HopfTranslate.translate_mem_of_isHopfOrder | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.HopfTranslate.translate_mem_of_isHopfOrder <;> assumption)
