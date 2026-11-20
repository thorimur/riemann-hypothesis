import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueChernClassNilpotentBase
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_chern_class_nilpotent_base : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (γ : DividedPowers I) (p : ℕ) (hp : p ≠ 0) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) (D : E.LineData X) (hD : sSup (𝒱D D) = ⊤) {Λ : Type} [CommRing Λ]
    (c : Λ →+* R) (N : ℕ), (N.factorial : R) = 0 →
    ∃! x, B.IsFirstChernClassOfLineBundle (q := q) (b := nlBase R I γ p) (ht := rfl) (κ := κ) D c N x := by
  first | exact @GlobalTheory.CompanionTheory.CrystallineChernClass.existsUnique_crystalline_chern_class | exact GlobalTheory.CompanionTheory.CrystallineChernClass.existsUnique_crystalline_chern_class | (intros; apply GlobalTheory.CompanionTheory.CrystallineChernClass.existsUnique_crystalline_chern_class <;> assumption)
