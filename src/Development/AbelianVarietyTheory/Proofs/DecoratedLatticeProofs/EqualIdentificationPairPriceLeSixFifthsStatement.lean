import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqualIdentificationPairPriceLeSixFifths
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equalIdentificationPairPrice_le_six_fifths : ∀ (C' Cl Cg cb Cw cT CT C0 : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X), Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → PgC Y ≤ 6 / 5 := by
  first | exact @GlobalTheory.Core.Deg.pgC_le_six_fifths | exact GlobalTheory.Core.Deg.pgC_le_six_fifths | (intros; apply GlobalTheory.Core.Deg.pgC_le_six_fifths <;> assumption)
