import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryAutomorphicCountingOfCompactDualVolumeRat
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAutomorphicCounting_of_compactDualVolumeRatio : GlobalTheory.FlagMeas.VolumeStep → GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem.CountingTheorem := by
  first | exact @GlobalTheory.CountFinal.countingTheorem_of_volumeStep | exact GlobalTheory.CountFinal.countingTheorem_of_volumeStep | (intros; apply GlobalTheory.CountFinal.countingTheorem_of_volumeStep <;> assumption)
