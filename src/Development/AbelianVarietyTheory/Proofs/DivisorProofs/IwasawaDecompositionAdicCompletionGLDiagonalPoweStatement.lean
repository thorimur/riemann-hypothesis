import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompositionAdicCompletionGLDiagonalPowe
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_decomposition_adicCompletionGL_diagonalPowers : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ g : GL (Fin a) (w.adicCompletion E), ∃ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a), ∃ (N : ℕ) (l : Fin a → ℕ), ∃ k ∈ KGL w a, g = u * GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ => N) * GlobalTheory.JSW.diagPow ϖ l * k := by
  first | exact @GlobalTheory.IwasawaGL.iwasawa_diagPow | exact GlobalTheory.IwasawaGL.iwasawa_diagPow | (intros; apply GlobalTheory.IwasawaGL.iwasawa_diagPow <;> assumption)
