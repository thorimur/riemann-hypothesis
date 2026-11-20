import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeLipschitzProperties
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncatedLeastLatticeSize_lipschitz_properties : TauLip := by
  first | exact @GlobalTheory.TauLipschitz.tauLip | exact GlobalTheory.TauLipschitz.tauLip | (intros; apply GlobalTheory.TauLipschitz.tauLip <;> assumption)
