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
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv

theorem one_tmul_quot_reduction :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (I : Ideal O),
      (∀ y : (O ⧸ I) ⊗[O] M, ∃ b : M, y = 1 ⊗ₜ b) ∧
      (∀ b : M, (1 : O ⧸ I) ⊗ₜ[O] b = 0 ↔ b ∈ I • (⊤ : Submodule O M)) ∧
      ∀ (a : O) (b : M), b ∈ Ideal.span {a} • (⊤ : Submodule O M) ↔ ∃ z, b = a • z := by
  intro O M _ _ _ I
  refine ⟨?_, ?_, ?_⟩
  · intro y
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective (I • (⊤ : Submodule O M))
      (TensorProduct.quotTensorEquivQuotSMul M I y)
    refine ⟨b, ?_⟩
    rw [← TensorProduct.quotTensorEquivQuotSMul_symm_mk I b, hb, LinearEquiv.symm_apply_apply]
  · intro b
    rw [← (TensorProduct.quotTensorEquivQuotSMul M I).map_eq_zero_iff,
      TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]
  · intro a b
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨z, -, hz⟩
      exact ⟨z, hz.symm⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, Submodule.mem_top, rfl⟩

end GlobalTheory.PDiv
