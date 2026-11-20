import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEqOfLe
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.btOrder_eq_of_le_of_isFinOpenSub : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U U' : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.IsFinOpenSub U' → U' ≤ U → Γ.btOrder U = Γ.btOrder U' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.QFGroup.btOrder_eq_of_le | exact GlobalTheory.CompanionTheory.Ar.BT.QFGroup.btOrder_eq_of_le | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.QFGroup.btOrder_eq_of_le <;> assumption)
