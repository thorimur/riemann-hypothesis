import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicPolynomialLattices
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_bound_tuple : GlobalTheory.BigOn.Exp.TupLe.SmallSt := by
  first | exact @GlobalTheory.SmallSpan.smallSt | exact GlobalTheory.SmallSpan.smallSt | (intros; apply GlobalTheory.SmallSpan.smallSt <;> assumption)
