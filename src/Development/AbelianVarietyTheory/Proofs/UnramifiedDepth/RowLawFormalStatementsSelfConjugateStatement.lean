import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RowLawFormalStatementsSelfConjugate
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowLaw_formal_statements_selfConjugate : CartSelfSt ∧ AxesSelfSt ∧ GermZeroSelfConjugate ∧ CEqSelfSt ∧ IndependenceBoundSelfConjugate := by
  first | exact @GlobalTheory.RowLaw.formal_statements_selfConj | exact GlobalTheory.RowLaw.formal_statements_selfConj | (intros; apply GlobalTheory.RowLaw.formal_statements_selfConj <;> assumption)
