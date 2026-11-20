import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockLowerBoundTorsion
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delta_block_lower_bound_torsion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (m : ℕ) (c : Matrix (Fin m) (Fin m) E), (∀ a b, σ (c b a) = c a b) → ∀ (u : Fin m → E) (t : 𝓞 E), t ∈ tor c u → t ≠ 0 → ∃ f : F, ∀ d : F, delta c * Ideal.absNorm (tor c u) ^ 2 * Ideal.absNorm (den F (f + ((RingOfIntegers.norm F t : 𝓞 F) : F) * d)) ^ 2 ≤ delta (blk σ c u (algebraMap F E d)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LocalBound.local_bound | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LocalBound.local_bound | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LocalBound.local_bound <;> assumption)
