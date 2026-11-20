import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StatementPrimeField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.statement_prime_field : GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps.StatementPrimeField := by
  first | exact @GlobalTheory.DegChTwo.statementPrimeField | exact GlobalTheory.DegChTwo.statementPrimeField | (intros; apply GlobalTheory.DegChTwo.statementPrimeField <;> assumption)
