import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NabIndepAndDelIndepLocalConditions
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nabIndep_and_delIndep_local_conditions : NabIndep ∧ DelIndep := by
  first | exact @GlobalTheory.TestLat.nabIndep_and_delIndep | exact GlobalTheory.TestLat.nabIndep_and_delIndep | (intros; apply GlobalTheory.TestLat.nabIndep_and_delIndep <;> assumption)
