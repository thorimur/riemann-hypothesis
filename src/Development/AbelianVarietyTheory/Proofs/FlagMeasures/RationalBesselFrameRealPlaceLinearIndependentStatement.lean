import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalBesselFrameRealPlaceLinearIndependent
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalBesselFrame_realPlace_linearIndependent : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (v : NumberField.InfinitePlace X.B.I.F), LinearIndependent ℂ (Formalism.L2.SG.RealObj.frm X u 1 v) := by
  first | exact @GlobalTheory.RationalFrame.frame_linearIndependent | exact GlobalTheory.RationalFrame.frame_linearIndependent | (intros; apply GlobalTheory.RationalFrame.frame_linearIndependent <;> assumption)
