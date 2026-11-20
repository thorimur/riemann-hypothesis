import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualIsotropicLineMemCompletionIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualIsotropicLine_mem_completion_iff : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ)
    (L : Lat S) (L₀ : Lat S₀) (𝔟 : ℕ → FI D) (v : Pl D), IsSelfDualC S L → MonoId d L L₀ 𝔟 v → ∀ i : Fin ρ, 𝔟 i ≠ 0 →
      ∀ t ∈ idAt D (· = v), colMul d.jY i t ∈ latV S L (· = v) ↔ cA D t ∈ idV (𝔟 i)⁻¹ v := by
  first | exact @GlobalTheory.DualLine.dualLine_mem_iff | exact GlobalTheory.DualLine.dualLine_mem_iff | (intros; apply GlobalTheory.DualLine.dualLine_mem_iff <;> assumption)
