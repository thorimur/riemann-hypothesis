import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiTripleProductTwoVariableTheta
open Complex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobiTripleProduct_twoVariableTheta : GlobalTheory.ThetaWeberRoad.TripleProduct := by
  first | exact @GlobalTheory.JacobiTriple.tripleProduct | exact GlobalTheory.JacobiTriple.tripleProduct | (intros; apply GlobalTheory.JacobiTriple.tripleProduct <;> assumption)
