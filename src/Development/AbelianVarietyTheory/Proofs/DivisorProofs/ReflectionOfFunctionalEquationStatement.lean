import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReflectionOfFunctionalEquation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reflection_of_functional_equation : GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.SqTop.FieldDat → GlobalTheory.SqTop.LNe → GlobalTheory.SqTop.Refl := by
  first | exact @GlobalTheory.SqTop.refl_of_functionalEquation | exact GlobalTheory.SqTop.refl_of_functionalEquation | (intros; apply GlobalTheory.SqTop.refl_of_functionalEquation <;> assumption)
