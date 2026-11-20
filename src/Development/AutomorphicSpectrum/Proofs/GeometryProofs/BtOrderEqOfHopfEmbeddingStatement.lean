import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEqOfHopfEmbedding
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.btOrder_eq_of_hopf_embedding : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (A : Subalgebra R (T → R)), IsHopfOrder A → ∀ (j : Γ.G.left ⟶ Spec (CommRingCat.of A)), Γ.IsEmb A j → IsOpenImmersion j → Γ.TranslatesCover A j ⊤ → Γ.btOrder ⊤ = A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.btOrder_eq_of_open_cover | exact GlobalTheory.CompanionTheory.Ar.BT.btOrder_eq_of_open_cover | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.btOrder_eq_of_open_cover <;> assumption)
