import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharContinuousNontrivial

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_char_continuous_nontrivial : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ v : Pl F,
    Continuous (psiLoc ψ v) ∧ ∃ x : Fv F v, psiLoc ψ v x ≠ 1 := by
  first | exact @GlobalTheory.PsiLocal.psi_loc_main | exact GlobalTheory.PsiLocal.psi_loc_main | (intros; apply GlobalTheory.PsiLocal.psi_loc_main <;> assumption)
