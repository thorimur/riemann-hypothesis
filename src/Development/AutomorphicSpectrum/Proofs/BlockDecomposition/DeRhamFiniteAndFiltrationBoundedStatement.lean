import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeRhamFiniteAndFiltrationBounded
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_finite_and_filtration_bounded : KH.LocGr → KH.LocVan → KH.PolyTf → KH.GlobSerreSt → KH.GlobVanSt → KH.KIso → KH.GrAff → KH.GrCechFin → ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q] (j : ℕ),
    FiniteDimensional K (HdR q j) ∧ ∀ x ∈ FilR q j (j + 1), x = 0 := by
  first | exact @GlobalTheory.CompanionTheory.KFin.main | exact GlobalTheory.CompanionTheory.KFin.main | (intros; apply GlobalTheory.CompanionTheory.KFin.main <;> assumption)
