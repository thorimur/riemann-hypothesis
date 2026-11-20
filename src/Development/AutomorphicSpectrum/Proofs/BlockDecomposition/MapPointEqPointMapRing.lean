import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints
import GroundTheory.GlobalFields.ComplexMultiplication.ReductionMap

open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

namespace GlobalTheory.CompanionTheory.ConjPointDict

theorem mapPoint_eq_pointMapRing : ∀ [DecidableEq ℂ] (X : WeierstrassCurve ℂ) (σ : ℂ →+* ℂ)
    (P : X.toAffine.Point), GlobalTheory.ConjPoint.mapPoint X σ P = GroundTheory.Global.pointMapRing σ X P := by
  intro _ X σ P
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · obtain ⟨h', e⟩ := GroundTheory.Global.pointMapRing_some σ X h
    rw [e]
    rfl

end GlobalTheory.CompanionTheory.ConjPointDict
