import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFiltrationVanishesAboveDimension
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_filtration_vanishes_above_dimension : KH.LocGr → KH.LocVan → KH.PolyTf → KH.GlobSerreSt → KH.GlobVanSt → KH.KIso → KH.GrAff → ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsProper q] (d : ℕ)
    [SmoothOfRelativeDimension d q] (j : ℕ), ∀ x ∈ FilR q j (d + 1), x = 0 := by
  first | exact @GlobalTheory.CompanionTheory.FilTop.fil_top_vanish | exact GlobalTheory.CompanionTheory.FilTop.fil_top_vanish | (intros; apply GlobalTheory.CompanionTheory.FilTop.fil_top_vanish <;> assumption)
