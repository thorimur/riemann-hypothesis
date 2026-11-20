import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

namespace GlobalTheory.InnerSumZeroSpan

theorem main : (let d1 : ℕ → Type := @(fun (n : ℕ) ↦ EuclideanSpace ℂ (Fin n)); ∀ {n : ℕ} (L M : d1 n →L[ℂ] d1 n) (s t : Set (d1 n)), (∀ u ∈ s, ∀ z ∈ t, Inner.inner ℂ ((L : d1 n → d1 n) u) z + Inner.inner ℂ u ((M : d1 n → d1 n) z) = (0 : ℂ)) → ∀ u ∈ Submodule.span ℂ s, ∀ z ∈ Submodule.span ℂ t, Inner.inner ℂ ((L : d1 n → d1 n) u) z + Inner.inner ℂ u ((M : d1 n → d1 n) z) = (0 : ℂ)) := by
  intro d1 n L M s t h u hu z hz
  induction hz using Submodule.span_induction with
  | mem z hz' =>
    induction hu using Submodule.span_induction with
    | mem u hu' => exact h u hu' z hz'
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add, inner_add_left, inner_add_left, add_add_add_comm, hx, hy, add_zero]
    | smul c x _ hx =>
      rw [map_smul, inner_smul_left, inner_smul_left, ← mul_add, hx, mul_zero]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, inner_add_right, inner_add_right, add_add_add_comm, hx, hy, add_zero]
  | smul c x _ hx =>
    rw [map_smul, inner_smul_right, inner_smul_right, ← mul_add, hx, mul_zero]

end GlobalTheory.InnerSumZeroSpan
