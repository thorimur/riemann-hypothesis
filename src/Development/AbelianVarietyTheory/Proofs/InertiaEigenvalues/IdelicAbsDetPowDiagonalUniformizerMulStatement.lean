import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdelicAbsDetPowDiagonalUniformizerMul
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idelicAbsDetPow_diagonalUniformizer_mul : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (x : ℝ) (g : GA E n),
    GlobalTheory.RSJ.detPow E n x (GlobalTheory.CellDec.tl n ϖ l * g) =
      (∏ w ∈ l.support, (qV E w : ℝ) ^ (-x * ∑ i, (l w i : ℝ))) * GlobalTheory.RSJ.detPow E n x g := by
  first | exact @GlobalTheory.CellEvalDet.detPow_tl_mul | exact GlobalTheory.CellEvalDet.detPow_tl_mul | (intros; apply GlobalTheory.CellEvalDet.detPow_tl_mul <;> assumption)
