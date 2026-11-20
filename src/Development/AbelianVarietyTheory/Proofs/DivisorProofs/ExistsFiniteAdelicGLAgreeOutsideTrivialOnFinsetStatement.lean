import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicGLAgreeOutsideTrivialOnFinset
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdelicGL_agree_outside_trivial_on_finset : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (k : GL (Fin a) (Af E)), ∃ k' : GL (Fin a) (Af E), (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k' = GeneralLinearGroup.map (pLoc E w) k) ∧ ∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k' = 1 := by
  first | exact @GlobalTheory.outsideS_elt | exact GlobalTheory.outsideS_elt | (intros; apply GlobalTheory.outsideS_elt <;> assumption)
