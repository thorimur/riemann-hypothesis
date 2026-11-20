import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqBesselFunctionLargeGaps
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitude_eq_besselFunction_largeGaps : GlobalTheory.GapIn.Hyp → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), 1000 ≤ Cl → D.host.rdE ≤ large₂.sc.b → m₀ ≤ D.R.m → cdScaleTie D → Bridge.AmpIsBessel D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Ca := by
  first | exact @GlobalTheory.AmpBesselGap.ampIsBessel | exact GlobalTheory.AmpBesselGap.ampIsBessel | (intros; apply GlobalTheory.AmpBesselGap.ampIsBessel <;> assumption)
