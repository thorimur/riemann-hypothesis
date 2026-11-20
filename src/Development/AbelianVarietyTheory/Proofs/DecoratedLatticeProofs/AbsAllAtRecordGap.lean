import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HypOfUniqGap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMultiplicityOneLargeGapAndWhittakerBessel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantLengthMomentsAmplitudesLargeGap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AbsRangeConstantsFirst
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ElementarySizeBoundsOfSizeHypotheses
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.BridgeLemma

namespace GlobalTheory.AbsRecGap

theorem abs_all_at_record_gap : ∀ Cg cb Cu cT CT C0 : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ Cn : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), thr ≤ C' → thr ≤ Cl → Formalism.MainNotions.BridgeLemma.AbsAllParameters D large₂ C' Cl Cg cb Cu cT CT C0 1 1 Cn C := by
  intro Cg cb Cu cT CT C0
  have hG : GlobalTheory.GapIn.Hyp := GlobalTheory.GapIn.hyp_of_uniqGap GlobalTheory.uniqGap_and_besselOfW.1
  obtain ⟨CMo, hMo⟩ := GlobalTheory.AmpMomentsGap.amplitude_moments_gap hG Cg cb Cu cT CT C0 1 25
  obtain ⟨C₀, hAbs⟩ := GlobalTheory.Amp.AbsRangeUniform.abs_range_constants_first Cg cb Cu cT CT 1 CMo
  obtain ⟨m₁, hAbs'⟩ := hAbs (max C₀ 0) (le_max_left _ _)
  refine ⟨max C₀ 0, le_max_right _ _, fun Cn => ?_⟩
  obtain ⟨m₂, hM⟩ := hMo Cn
  obtain ⟨thr, hthr⟩ := GlobalTheory.Core.Deg.elementary_size_bounds_of_size_hypotheses (max (max m₁ m₂) 1000)
  refine ⟨thr, ?_⟩
  intro D large₂ C' Cl hC' hCl τ w w' hTT θ hθ W hW lam' hl S hS γ p hp θ' hθ' νR hR hHyp hD
  have h0 : GlobalTheory.Amp.HypZ D large₂ C' Cl Cg cb Cu cT CT C0 := by
    unfold Formalism.MainNotions.S.Cnt.Hyp at hHyp; exact hHyp.1
  obtain ⟨h1000, -, hm, -, hrd, -⟩ := hthr D large₂ C' Cl Cg cb Cu cT CT hC' hCl h0.1
  have hm1000 : (1000 : ℝ) ≤ (D.R.m : ℝ) := le_trans (le_max_right _ _) hm
  have hB : ∀ m₀, m₀ ≤ max (max m₁ m₂) 1000 → GlobalTheory.Amp.Big D large₂ Cl m₀ :=
    fun m₀ h => ⟨hrd, by nlinarith, le_trans h hm⟩
  exact (hAbs' Cn D large₂ C' Cl C0 (hB _ (le_trans (le_max_left _ _) (le_max_left _ _)))
    (hM D large₂ C' Cl h1000 (hB _ (le_trans (le_max_right _ _) (le_max_left _ _))))
    h0 τ w w' hTT θ hθ W hW lam' hl S hS γ p hp θ' hθ' νR hR hD).2

end GlobalTheory.AbsRecGap
