import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowFormsMatchPeriodMapOfFurtherProperties
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowFormsMatchPeriodMap_of_furtherProperties : ∀ (K : Ctx) (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0), RX K B f T w Z Wt p0 t → ∀ a, GlobalTheory.AtG.RowPin w.I w.ok w.l Z a := by
  first | exact @GlobalTheory.AtG.RX.rowPin_of_rx | exact GlobalTheory.AtG.RX.rowPin_of_rx | (intros; apply GlobalTheory.AtG.RX.rowPin_of_rx <;> assumption)
