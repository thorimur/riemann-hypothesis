import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalTheoremOfFourPointBounds
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalTheorem_of_fourPointBounds : ∀ (D : D7) (c : Formalism.L2.SG.ThmSOwn.ConcK D) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Γ₁ Γ₂ Γ : ℝ) (u : D.what₂.Word), 29 ≤ C' → 29 ≤ Cl → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → 0 ≤ Γ₁ → 0 ≤ Γ₂ → Γ₁ + Γ₂ ≤ Γ → VanishingGramTermsBound c.Y u → CollS c.Y u → (c.Y.tO u u).pairSum ((c.Y.tO u u).one (c.Y.tO u u).genSet) ≤ Γ₁ * ddC c.X c.Y u u → (c.Y.tO u u).pairSum ((c.Y.tO u u).one (c.Y.tO u u).ngSet) ≤ Γ₂ * ddC c.X c.Y u u → SDiagAt D u Γ (1 / 2) := by
  first | exact @GlobalTheory.Core.Diag.sDiagAt_of_points | exact GlobalTheory.Core.Diag.sDiagAt_of_points | (intros; apply GlobalTheory.Core.Diag.sDiagAt_of_points <;> assumption)
