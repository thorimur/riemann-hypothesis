import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelBoundGivesConstantBound
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_bound_gives_constant_bound : Hypotheses2 → HypothesesH → GlobalTheory.Published.DemaillyRegularisation → KernelSt → ConstSt := by
  first | exact @GlobalTheory.ConstServe.constSt | exact GlobalTheory.ConstServe.constSt | (intros; apply GlobalTheory.ConstServe.constSt <;> assumption)
