import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import GroundTheory.GlobalFields.TateThesis.HeckeTheoremScaling
open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem discrNormConductor_eq_dF_of_unramified :
    ∀ (F : Type) [Field F] [NumberField F] (χ : HeckeCharacter F),
      standardOpenSubgroup F ≤ χ.toIdele.ker → χ.discrNormConductor = GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F := by
  intro F _ _ χ hχ
  have htop : χ.conductor = ⊤ := by
    have h := (χ.map_idealLevel_le_ker_iff (𝔪 := ⊤) top_ne_bot).1
      ((map_idealLevel_le_standardOpenSubgroup ⊤).trans hχ)
    rw [Ideal.dvd_iff_le, top_le_iff] at h
    exact h
  rw [HeckeCharacter.discrNormConductor, htop, Ideal.absNorm_top, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF]
  simp

end GlobalTheory.CompanionTheory.PartialZeta
