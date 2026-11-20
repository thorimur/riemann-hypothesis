import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealBesselSubgroupActsFrameUpperUnitriangular
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realBesselSubgroup_acts_frame_upperUnitriangular : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (y : X.B.I.Ginf), y ∈ X.SinfU u → ∀ v : NumberField.InfinitePlace X.B.I.F, ∃ M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ, IsUpUni M ∧ GlobalTheory.LoopAct.IsMatOn (uMat (y v)) (Formalism.L2.SG.RealObj.frm X u 1 v) M := by
  first | exact @GlobalTheory.LoopAct.sinfU_frame_upUni | exact GlobalTheory.LoopAct.sinfU_frame_upUni | (intros; apply GlobalTheory.LoopAct.sinfU_frame_upUni <;> assumption)
