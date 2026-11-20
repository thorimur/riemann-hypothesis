import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extension_statement : GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.Extension := by
  first | exact @GlobalTheory.ExtLogGrowth.extension_of_log_growth | exact GlobalTheory.ExtLogGrowth.extension_of_log_growth | (intros; apply GlobalTheory.ExtLogGrowth.extension_of_log_growth <;> assumption)
