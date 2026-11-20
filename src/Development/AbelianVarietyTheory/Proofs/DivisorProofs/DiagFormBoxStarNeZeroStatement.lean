import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagFormBoxStarNeZero

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diag_form_box_star_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (φ : (κ → AF F) → ℂ),
    φ ∈ schA F κ → φ ≠ 0 → GlobalTheory.DiagForm.lDiag F κ (boxFun φ (star φ)) ≠ 0 := by
  first | exact @GlobalTheory.DiagSq.lDiag_boxFun_star_ne | exact GlobalTheory.DiagSq.lDiag_boxFun_star_ne | (intros; apply GlobalTheory.DiagSq.lDiag_boxFun_star_ne <;> assumption)
