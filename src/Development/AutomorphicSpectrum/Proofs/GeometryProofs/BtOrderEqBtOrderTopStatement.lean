import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEqBtOrderTop
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.btOrder_eq_btOrder_top : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.btOrder U = Γ.btOrder ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Relay.btOrder_eq_btOrder_top | exact GlobalTheory.CompanionTheory.Relay.btOrder_eq_btOrder_top | (intros; apply GlobalTheory.CompanionTheory.Relay.btOrder_eq_btOrder_top <;> assumption)
