import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeCompressionFormulaOfStrictLowestKType
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowestKType_compressionFormula_of_strictLowestKType : FormulaGap := by
  first | exact @GlobalTheory.Jet.FormGapFree.formulaGap | exact GlobalTheory.Jet.FormGapFree.formulaGap | (intros; apply GlobalTheory.Jet.FormGapFree.formulaGap <;> assumption)
