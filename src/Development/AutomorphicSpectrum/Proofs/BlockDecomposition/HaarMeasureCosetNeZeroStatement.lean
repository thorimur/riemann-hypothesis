import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureCosetNeZero
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_measure_coset_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure] (c : k), c ≠ 0 → (((μ (cosetSet t c 0)).toReal : ℝ) : ℂ) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.volume_cosetSet_ne_zero | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.volume_cosetSet_ne_zero | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.volume_cosetSet_ne_zero <;> assumption)
