import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowStatementOfConstants
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.low_statement_of_constants : Hypotheses2 → HypothesesH → KernelSt → SizeSt → ConstSt → LowSt := by
  first | exact @GlobalTheory.RegLow.lowSt | exact GlobalTheory.RegLow.lowSt | (intros; apply GlobalTheory.RegLow.lowSt <;> assumption)
