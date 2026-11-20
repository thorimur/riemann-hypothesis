import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharacterSectionMultiplicative
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_section_multiplicative : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤)), Γ.HasValues s (fun t => ((χ t : Rˣ) : R)) → ∀ (Y : Over (Spec (CommRingCat.of R))), (∀ y z : Y ⟶ Γ.G, (y * z).left.appTop s = y.left.appTop s * z.left.appTop s) ∧ (1 : Y ⟶ Γ.G).left.appTop s = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.charValues_mul | exact GlobalTheory.CompanionTheory.Ar.BT.charValues_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.charValues_mul <;> assumption)
