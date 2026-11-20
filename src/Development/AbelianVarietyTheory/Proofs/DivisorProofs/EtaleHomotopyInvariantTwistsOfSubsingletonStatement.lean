import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfSubsingleton
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHomotopyInvariantTwists_of_subsingleton : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], Subsingleton A → HInv q A := by
  first | exact @GlobalTheory.EtC.hInv_of_subsingleton | exact GlobalTheory.EtC.hInv_of_subsingleton | (intros; apply GlobalTheory.EtC.hInv_of_subsingleton; all_goals assumption)
