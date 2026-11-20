import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricDenominatorOfZetaDenominators
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toric_denominator_of_zeta_denominators : GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators → LatIntRam → LatIntUnr → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator := by
  first | exact @GlobalTheory.ToricDenomRow.toricDenominator | exact GlobalTheory.ToricDenomRow.toricDenominator | (intros; apply GlobalTheory.ToricDenomRow.toricDenominator <;> assumption)
