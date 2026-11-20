import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockMatrixMultiplicative
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delta_block_matrix_multiplicative : ∀ (F E : Type) [Field F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (m : ℕ) (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E), delta (blk σ c u d) = delta c * Ideal.absNorm (tor c u) * idx E (lastFib (blk σ c u d)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.IndexFormula.delta_blk | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.IndexFormula.delta_blk | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.IndexFormula.delta_blk <;> assumption)
