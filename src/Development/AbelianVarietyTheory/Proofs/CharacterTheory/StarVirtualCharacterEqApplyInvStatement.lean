import Development.AbelianVarietyTheory.Proofs.CharacterTheory.StarVirtualCharacterEqApplyInv
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.star_virtualCharacter_eq_apply_inv : ∀ (G : Type) [Group G] [Finite G] (χ : G → ℂ), χ ∈ Virt ℂ ℂ G → ∀ g, star (χ g) = χ g⁻¹ := by
  first | exact @GlobalTheory.CuspGL.star_virt_eq_inv | exact GlobalTheory.CuspGL.star_virt_eq_inv | (intros; apply GlobalTheory.CuspGL.star_virt_eq_inv <;> assumption)
