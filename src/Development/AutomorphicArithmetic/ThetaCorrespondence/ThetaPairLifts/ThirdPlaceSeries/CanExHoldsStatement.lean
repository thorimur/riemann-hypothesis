import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CanExHolds

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigOn_canEx : _root_.GlobalTheory.BigOn.Exp.CanonicalExists := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.canEx_holds_alt | exact _root_.GlobalTheory.BigOn.Exp.canEx_holds_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.canEx_holds_alt <;> assumption)
end
