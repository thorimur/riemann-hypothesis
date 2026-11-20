import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersDivPushForwardLocal
set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DivPushForward.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.DivPushForward.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.DivPushForward.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelDimLe.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DivPushForwardLocal
