import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalRowOfSiegelWeilUnitary
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalRow_of_siegelWeil_unitary : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → GlobalTheory.Core.Rk.RowDiag (fun D L C' => GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) := by
  first | exact @GlobalTheory.Core.Rk.rowDiag_of_siegelWeilUnitary | exact GlobalTheory.Core.Rk.rowDiag_of_siegelWeilUnitary | (intros; apply GlobalTheory.Core.Rk.rowDiag_of_siegelWeilUnitary <;> assumption)
