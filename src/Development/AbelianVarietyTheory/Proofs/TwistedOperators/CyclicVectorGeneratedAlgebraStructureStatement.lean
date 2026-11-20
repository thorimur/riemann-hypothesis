import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorGeneratedAlgebraStructure
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclicVector_generatedAlgebra_structure : GlobalTheory.RegSS.CyclicAlgebra := by
  first | exact @GlobalTheory.RegSS.CycAlg.cyclicAlgebra | exact GlobalTheory.RegSS.CycAlg.cyclicAlgebra | (intros; apply GlobalTheory.RegSS.CycAlg.cyclicAlgebra <;> assumption)
