import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UniformAmplitudeBoundWideRangeLargeGap
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_amplitude_bound_wide_range_large_gap : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cn, (OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.adm1 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C) := by
  first | exact @GlobalTheory.UnifPTGap.uniformPT_gap | exact GlobalTheory.UnifPTGap.uniformPT_gap | (intros; apply GlobalTheory.UnifPTGap.uniformPT_gap <;> assumption)
