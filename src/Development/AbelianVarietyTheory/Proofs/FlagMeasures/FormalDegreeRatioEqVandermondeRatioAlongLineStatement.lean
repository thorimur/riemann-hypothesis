import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeRatioEqVandermondeRatioAlongLine
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalDegree_ratio_eq_vandermonde_ratio_along_line : ∀ Cn : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 C1 : ℝ), thr ≤ C' → thr ≤ Cl → Ties D → BridgeLemma₂.deg_VandLine D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 := by
  first | exact @GlobalTheory.DegLine.deg_VandLine_of_gap | exact GlobalTheory.DegLine.deg_VandLine_of_gap | (intros; apply GlobalTheory.DegLine.deg_VandLine_of_gap <;> assumption)
