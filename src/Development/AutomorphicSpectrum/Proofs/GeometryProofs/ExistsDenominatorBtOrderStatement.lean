import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDenominatorBtOrder
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_denominator_btOrder : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), ∃ d : R, d ≠ 0 ∧ ∀ f : T → R, d • f ∈ Γ.btOrder ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.btOrder_full_rank | exact GlobalTheory.CompanionTheory.Ar.BT.btOrder_full_rank | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.btOrder_full_rank <;> assumption)
