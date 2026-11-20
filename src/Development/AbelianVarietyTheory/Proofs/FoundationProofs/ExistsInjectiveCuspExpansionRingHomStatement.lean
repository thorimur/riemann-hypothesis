import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsInjectiveCuspExpansionRingHom
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_cuspExpansion_ringHom : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), ∃ e : GlobalTheory.FN.ring ε.range →+* HahnSeries ℚ Ω, Function.Injective e ∧ ∀ a : GlobalTheory.FN.ring ε.range, IsExp ε a (e a) := by
  first | exact @GlobalTheory.FN.expansion_injective_ringHom | exact GlobalTheory.FN.expansion_injective_ringHom | (intros; apply GlobalTheory.FN.expansion_injective_ringHom <;> assumption)
