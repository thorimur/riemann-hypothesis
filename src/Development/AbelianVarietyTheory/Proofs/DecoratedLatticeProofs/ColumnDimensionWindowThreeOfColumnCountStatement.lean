import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColumnDimensionWindowThreeOfColumnCount
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnDimension_window_three_of_columnCount : ∀ D : D7, DataNW D → (∀ u, GlobalTheory.Core.Rk.RankMu D u) → StandingNumericalData D 3 := by
  first | exact @GlobalTheory.Core.Diag.standingNumericalData_three_of_dataNW_rankMu | exact GlobalTheory.Core.Diag.standingNumericalData_three_of_dataNW_rankMu | (intros; apply GlobalTheory.Core.Diag.standingNumericalData_three_of_dataNW_rankMu <;> assumption)
