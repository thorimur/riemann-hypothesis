import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MonomialBlockSupplyBothTypings
open Formalism.L2.FormalSeriesBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monomialBlock_supply_both_typings : MONSupply ∧ RF.MONSupply := by
  first | exact @GlobalTheory.MonBlock.monSupply | exact GlobalTheory.MonBlock.monSupply | (intros; apply GlobalTheory.MonBlock.monSupply <;> assumption)
