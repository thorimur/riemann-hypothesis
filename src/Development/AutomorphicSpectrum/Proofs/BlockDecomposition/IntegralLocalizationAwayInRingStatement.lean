import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralLocalizationAwayInRing
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_localization_away_in_ring : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ nonZeroDivisors S → Val ϖ → ∀ x : Localization.Away ϖ, IsIntegral S x → ∃ y : S, algebraMap S (Localization.Away ϖ) y = x := by
  first | exact @GlobalTheory.CompanionTheory.ValIntClosed.exists_eq_of_isIntegral | exact GlobalTheory.CompanionTheory.ValIntClosed.exists_eq_of_isIntegral | (intros; apply GlobalTheory.CompanionTheory.ValIntClosed.exists_eq_of_isIntegral <;> assumption)
