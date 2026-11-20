import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlaceStandardCharLocallyConstantNontrivial
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePlace_standardChar_locallyConstant_nontrivial : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), ∃ ψ : AddChar (w.adicCompletion E) ℂ, (∀ x, ψ x = GlobalTheory.JSW.psiLoc w x) ∧ IsLocallyConstant ψ ∧ ψ ≠ 1 := by
  first | exact @GlobalTheory.JSW.psiLoc_addChar_locallyConstant_ne_one | exact GlobalTheory.JSW.psiLoc_addChar_locallyConstant_ne_one | (intros; apply GlobalTheory.JSW.psiLoc_addChar_locallyConstant_ne_one <;> assumption)
