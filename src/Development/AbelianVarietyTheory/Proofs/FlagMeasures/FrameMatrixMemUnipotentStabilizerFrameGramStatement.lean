import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameMatrixMemUnipotentStabilizerFrameGram
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameMatrix_mem_unipotentStabilizer_frameGram : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (γ y : X.B.I.Ginf) (v : NumberField.InfinitePlace X.B.I.F) (M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ), y ∈ Formalism.L2.SG.RealObj.StInf X u u' γ → IsUpUni M → GlobalTheory.LoopAct.IsMatOn (uMat ((γ⁻¹ * y * γ) v)) (Formalism.L2.SG.RealObj.frm X u' 1 v) M → IsUnit (Formalism.L2.SG.RealObj.ZX X u u' 1 γ v).det → M ∈ GlobalTheory.LoopV.stabU (Formalism.L2.SG.RealObj.ZX X u u' 1 γ v) := by
  first | exact @GlobalTheory.FrameStab.frameMat_mem_stabU | exact GlobalTheory.FrameStab.frameMat_mem_stabU | (intros; apply GlobalTheory.FrameStab.frameMat_mem_stabU <;> assumption)
