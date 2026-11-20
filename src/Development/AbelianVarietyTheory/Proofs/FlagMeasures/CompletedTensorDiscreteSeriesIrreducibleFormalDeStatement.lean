import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompletedTensorDiscreteSeriesIrreducibleFormalDe
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedTensorDiscreteSeries_irreducible_formalDegree : TensorRep := by
  first | exact @GlobalTheory.Dec.tensorRep | exact GlobalTheory.Dec.tensorRep | (intros; apply GlobalTheory.Dec.tensorRep <;> assumption)
