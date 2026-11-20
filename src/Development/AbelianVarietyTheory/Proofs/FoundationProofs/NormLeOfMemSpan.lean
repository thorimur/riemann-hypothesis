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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory.NormBoundOfSpan

theorem norm_le_of_mem_span {K E ι : Type} [NormedField K] [AddCommGroup E] [Module K E]
    (φ : ι → E →ₗ[K] K) :
    ∀ f ∈ Submodule.span K (Set.range φ), ∃ (C : ℝ), (0 : ℝ) ≤ C ∧ ∀ (p : E) (r : ℝ),
      (0 : ℝ) ≤ r → (∀ (j : ι), ‖(φ j : E → K) p‖ ≤ r) → ‖(f : E → K) p‖ ≤ C * r := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact ⟨1, zero_le_one, fun p r _ h => by simpa using h j⟩
  | zero => exact ⟨0, le_rfl, fun p r _ _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨C, hC, h1⟩ := hx
    obtain ⟨D, hD, h2⟩ := hy
    refine ⟨C + D, add_nonneg hC hD, fun p r hr h => ?_⟩
    rw [LinearMap.add_apply, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (h1 p r hr h) (h2 p r hr h))
  | smul a x _ hx =>
    obtain ⟨C, hC, h1⟩ := hx
    refine ⟨‖a‖ * C, mul_nonneg (norm_nonneg a) hC, fun p r hr h => ?_⟩
    rw [LinearMap.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h1 p r hr h) (norm_nonneg a)

end GlobalTheory.NormBoundOfSpan
