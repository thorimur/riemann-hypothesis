import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfClosedCover
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHomotopyInvariantTwists_of_closedCover : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (I J : Ideal A), I ⊓ J ≤ nilradical A → IsUnit (q : A) → HInv q (A ⧸ I) → HInv q (A ⧸ J) → HInv q (A ⧸ (I ⊔ J)) → HInv q A := by
  first | (exact @GlobalTheory.EtC.ClosedCover.closedCover) | (exact GlobalTheory.EtC.ClosedCover.closedCover) | (intros; apply GlobalTheory.EtC.ClosedCover.closedCover  <;> assumption)
