import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticeTermAdaptedNormalForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowLattice_term_adaptedNormalForm : GlobalTheory.TypeAsm.TermC := by
  first | exact @GlobalTheory.TermRow.termC_holds | exact GlobalTheory.TermRow.termC_holds | (intros; apply GlobalTheory.TermRow.termC_holds <;> assumption)
