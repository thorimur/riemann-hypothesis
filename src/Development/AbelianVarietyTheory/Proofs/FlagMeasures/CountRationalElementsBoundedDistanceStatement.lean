import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountRationalElementsBoundedDistance
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.count_rational_elements_bounded_distance : CountRat := by
  first | exact @GlobalTheory.Dec.BoundedDistance.countRat | exact GlobalTheory.Dec.BoundedDistance.countRat | (intros; apply GlobalTheory.Dec.BoundedDistance.countRat <;> assumption)
