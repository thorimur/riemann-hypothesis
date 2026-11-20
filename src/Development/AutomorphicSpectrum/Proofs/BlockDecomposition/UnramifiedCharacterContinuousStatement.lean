import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCharacterContinuous
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_character_continuous : ∀ (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (n : ℕ) [NeZero n] (χ : Gal(Ω/K) → ZMod n), (∀ g h, χ (g * h) = χ g + χ h) → (∀ g, unramifiedDegree K Ω g = Multiplicative.ofAdd 1 → χ g = 1) → Continuous χ := by
  first | exact @GlobalTheory.CompanionTheory.LocalUnram.continuous_of_additive_of_frobenius_eq_one | exact GlobalTheory.CompanionTheory.LocalUnram.continuous_of_additive_of_frobenius_eq_one | (intros; apply GlobalTheory.CompanionTheory.LocalUnram.continuous_of_additive_of_frobenius_eq_one <;> assumption)
