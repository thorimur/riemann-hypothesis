import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeMassRatio
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalHermitianLattice_massRatio : MaxMass := by
  first | exact @GlobalTheory.Mass.MaxFormula.main | exact GlobalTheory.Mass.MaxFormula.main | (intros; apply GlobalTheory.Mass.MaxFormula.main <;> assumption)
