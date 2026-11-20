import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteOpenHopfOrder
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_open_hopf_order : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → ∃ (H : Subgroup T) (A : Subalgebra R (H → R)), (∀ t, t ∈ H ↔ ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U) ∧ IsHopfOrder A ∧ ∀ f : H → R, f ∈ A ↔ ∃ s : Γ(Γ.G.left, U), ∀ (t : H) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = algebraMap R _ (f t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.SubOrder.hopfOrder_of_finOpenSub | exact GlobalTheory.CompanionTheory.Ar.BT.SubOrder.hopfOrder_of_finOpenSub | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.SubOrder.hopfOrder_of_finOpenSub <;> assumption)
