import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryLatticeCountRatioTendsto
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_lattice_count_ratio_tendsto : UnitaryLimit := by
  first | exact @GlobalTheory.UnitLemma.unitaryLimit | exact GlobalTheory.UnitLemma.unitaryLimit | (intros; apply GlobalTheory.UnitLemma.unitaryLimit <;> assumption)
