import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramPoincareHilbertSchmidtDeviationLeSplit
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramPoincareHilbertSchmidtDeviation_le_split : ∀ (D : D7) (u : D.what₂.Word), GlobalTheory.Core.Rk.hsDev D u ≤ 3 / 2 * hsNormSq (Kmat D.s u u - AdmissibleBoundsFromSource.Kpp D u u - ContinuousLinearMap.id ℂ (D.s.Cu u)) + 3 * hsNormSq (AdmissibleBoundsFromSource.Kpp D u u) := by
  first | exact @GlobalTheory.Core.Rk.hsDev_le_split_three_halves | exact GlobalTheory.Core.Rk.hsDev_le_split_three_halves | (intros; apply GlobalTheory.Core.Rk.hsDev_le_split_three_halves <;> assumption)
