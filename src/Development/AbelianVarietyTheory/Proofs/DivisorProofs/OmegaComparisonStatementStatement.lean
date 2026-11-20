import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaComparisonStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.omega_comparison_statement : Hypotheses2 → HypothesesH → OmCmp := by
  first | exact @GlobalTheory.OmCmpProof.om_cmp | exact GlobalTheory.OmCmpProof.om_cmp | (intros; apply GlobalTheory.OmCmpProof.om_cmp <;> assumption)
