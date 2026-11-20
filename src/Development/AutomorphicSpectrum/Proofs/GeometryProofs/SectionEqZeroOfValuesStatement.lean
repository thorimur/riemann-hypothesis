import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionEqZeroOfValues
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_eq_zero_of_values : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (s : Γ(Γ.G.left, U)), (∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = 0) → s = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.section_eq_zero_of_val_generic | exact GlobalTheory.CompanionTheory.Ar.BT.section_eq_zero_of_val_generic | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.section_eq_zero_of_val_generic <;> assumption)
