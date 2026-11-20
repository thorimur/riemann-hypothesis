import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagFormBoxConjNeZero

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixXChar GlobalTheory.DblEval
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diag_form_box_conj_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (g : (κ → AF F) → ℂ),
    g ∈ schA F κ → g ≠ 0 → GlobalTheory.DiagForm.lDiag F κ (boxFun g (fun x => starRingEnd ℂ (g x))) ≠ 0 := by
  first | exact @GlobalTheory.DiagPos.lDiag_box_conj_ne_zero | exact GlobalTheory.DiagPos.lDiag_box_conj_ne_zero | (intros; apply GlobalTheory.DiagPos.lDiag_box_conj_ne_zero <;> assumption)
