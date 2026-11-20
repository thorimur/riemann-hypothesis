import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NcardRationalPointsInTranslateLeHeightPow

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ncard_rational_points_in_translate_le_height_pow : ∀ {D : D7} {V : HSp D} {Ω : Set (GA D V)}, IsCompact Ω → ∃ (A : ℕ) (C : ℝ), ∀ g x : GA D V, {γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.Finite ∧ ({γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.ncard : ℝ) ≤ C * GlobalTheory.Grow.height V g ^ (2 * A) := by
  first | exact @GlobalTheory.RatCount.ncard_rat_mem_translate_le | exact GlobalTheory.RatCount.ncard_rat_mem_translate_le | (intros; apply GlobalTheory.RatCount.ncard_rat_mem_translate_le <;> assumption)
