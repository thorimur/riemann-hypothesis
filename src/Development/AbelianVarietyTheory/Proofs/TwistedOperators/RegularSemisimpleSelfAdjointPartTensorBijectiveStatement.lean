import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleSelfAdjointPartTensorBijective
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularSemisimple_selfAdjointPart_tensor_bijective : GlobalTheory.RegSS.PlusTensorBijective := by
  first | exact @GlobalTheory.RegSS.plusTensorBijective | exact GlobalTheory.RegSS.plusTensorBijective | (intros; apply GlobalTheory.RegSS.plusTensorBijective <;> assumption)
