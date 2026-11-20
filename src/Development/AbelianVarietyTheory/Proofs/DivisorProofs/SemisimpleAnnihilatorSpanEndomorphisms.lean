import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory

theorem semisimple_mem_sum_endo_images (R : Type) [Ring R] (M : Type) [AddCommGroup M] [Module R M]
    (hM : IsSemisimpleModule R M) (n : ℕ) (w : Fin n → M) (v : M)
    (h : ∀ a : R, (∀ j, a • w j = 0) → a • v = 0) :
    ∃ f : Fin n → (M →ₗ[R] M), v = ∑ j, f j (w j) := by
  have : IsSemisimpleModule R (Fin n → M) := inferInstance
  set A := LinearMap.toSpanSingleton R (Fin n → M) w with hA
  set B := LinearMap.toSpanSingleton R M v with hB
  have hk : LinearMap.ker A ≤ LinearMap.ker B := by
    intro a ha
    simp only [LinearMap.mem_ker, hA, hB, LinearMap.toSpanSingleton_apply] at ha ⊢
    apply h a
    intro j
    have := congrFun ha j
    simpa using this
  let φ : LinearMap.range A →ₗ[R] M :=
    (Submodule.liftQ _ B hk) ∘ₗ (LinearMap.quotKerEquivRange A).symm.toLinearMap
  obtain ⟨F, hF⟩ := IsSemisimpleModule.extension_property (LinearMap.range A).subtype
    (Submodule.injective_subtype _) φ
  refine ⟨fun j => F ∘ₗ LinearMap.single R (fun _ => M) j, ?_⟩
  have hw : w ∈ LinearMap.range A := ⟨1, by simp [hA]⟩
  have h1 : F w = v := by
    have := LinearMap.congr_fun hF ⟨w, hw⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this]
    have e : (LinearMap.quotKerEquivRange A).symm ⟨w, hw⟩ = Submodule.Quotient.mk 1 := by
      rw [LinearEquiv.symm_apply_eq]
      ext1
      simp [hA]
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe, e, Submodule.liftQ_apply, hB,
      LinearMap.toSpanSingleton_apply, one_smul]
  rw [← h1]
  conv_lhs => rw [← Finset.univ_sum_single w]
  simp [map_sum]

end GlobalTheory
