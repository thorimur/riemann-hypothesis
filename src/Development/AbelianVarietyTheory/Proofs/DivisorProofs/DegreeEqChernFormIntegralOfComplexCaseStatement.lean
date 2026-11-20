import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeEqChernFormIntegralOfComplexCase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degreeEqChernFormIntegral_of_complex_case : GlobalTheory.Published.ChernDegreeComplex → GlobalTheory.Published.ChernDegree := by
  first | exact @GlobalTheory.ChernDegreeBaseChange.chernDegree_of_complex | exact GlobalTheory.ChernDegreeBaseChange.chernDegree_of_complex | (intros; apply GlobalTheory.ChernDegreeBaseChange.chernDegree_of_complex <;> assumption)
