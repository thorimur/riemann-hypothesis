import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AbstractDiagonalBoundCollisionsCountedOnce
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abstractDiagonalBound_collisions_counted_once : ∀ (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] (X : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (one : H) (Pg B A₁ A₂ : ℝ), 0 ≤ Pg → X.AbsConv → X.NormExpansionOn X.genSet → X.NormExpansionOn X.ngSet → X.GGBound Pg → X.RowOrth → X.CorankPos → Formalism.L2.SG.RowsOther.IdOne X one → X.pairAbs (X.big X.nzSet) ≤ B → X.pairSum (X.one X.genSet) ≤ A₁ → X.pairSum (X.one X.ngSet) ≤ A₂ → ‖X.K0 - one‖ ^ 2 ≤ 2 * Pg * (B + A₁ + A₂) := by
  first | exact @GlobalTheory.diag_abstract_collisions_once | exact GlobalTheory.diag_abstract_collisions_once | (intros; apply GlobalTheory.diag_abstract_collisions_once <;> assumption)
