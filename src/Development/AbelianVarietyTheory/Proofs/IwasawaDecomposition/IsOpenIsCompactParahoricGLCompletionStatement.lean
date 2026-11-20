import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenIsCompactParahoricGLCompletion
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_isCompact_parahoric_GL_completion : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (r c : ℕ), IsOpen (parJ (OP P) (piP P : P.adicCompletion L) r c) ∧ IsCompact (parJ (OP P) (piP P : P.adicCompletion L) r c) := by
  first | exact @GlobalTheory.ParahoricTopo.isOpen_isCompact_parJ | exact GlobalTheory.ParahoricTopo.isOpen_isCompact_parJ | (intros; apply GlobalTheory.ParahoricTopo.isOpen_isCompact_parJ <;> assumption)
