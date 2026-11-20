import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderIsHopfOrder
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.btOrder_isHopfOrder : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → IsHopfOrder (Γ.btOrder U) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.btOrder_isHopfOrder_of_finOpenSub | exact GlobalTheory.CompanionTheory.Ar.BT.btOrder_isHopfOrder_of_finOpenSub | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.btOrder_isHopfOrder_of_finOpenSub <;> assumption)
