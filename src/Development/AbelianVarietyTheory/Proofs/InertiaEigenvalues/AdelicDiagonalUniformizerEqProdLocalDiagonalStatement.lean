import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicDiagonalUniformizerEqProdLocalDiagonal
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicDiagonalUniformizer_eq_prod_localDiagonal : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (l' : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℕ)),
    (∀ w i, ((l' w i : ℕ) : ℤ) = l w i) → GlobalTheory.CellDec.tl n ϖ l = GlobalTheory.JSW.tl ϖ l' := by
  first | exact @GlobalTheory.CellDecNat.tl_eq_jsw_tl | exact GlobalTheory.CellDecNat.tl_eq_jsw_tl | (intros; apply GlobalTheory.CellDecNat.tl_eq_jsw_tl <;> assumption)
