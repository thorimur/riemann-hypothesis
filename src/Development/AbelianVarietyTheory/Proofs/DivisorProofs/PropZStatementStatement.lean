import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PropZStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prop_z_statement : GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.PropZ := by
  first | exact @GlobalTheory.PropZRow.propZ | exact GlobalTheory.PropZRow.propZ | (intros; apply GlobalTheory.PropZRow.propZ <;> assumption)
