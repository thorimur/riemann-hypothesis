import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProductFieldsBaseChangeIsFieldIff
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_fields_baseChange_isField_iff : GlobalTheory.RegSS.TensorFieldIff := by
  first | exact @GlobalTheory.RegSS.tensorFieldIff | exact GlobalTheory.RegSS.tensorFieldIff | (intros; apply GlobalTheory.RegSS.tensorFieldIff <;> assumption)
