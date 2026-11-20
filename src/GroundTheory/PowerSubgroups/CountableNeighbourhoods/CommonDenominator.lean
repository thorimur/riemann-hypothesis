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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace GroundTheory.Variant₂.N1

open NumberField

theorem exists_common_denominator {K : Type} [Field K] [NumberField K] {N : ℕ}
    {M : Submodule (𝓞 K) (Fin N → K)} (hM : M.FG) :
    ∃ c : 𝓞 K, c ≠ 0 ∧ ∀ v ∈ M, ∀ i : Fin N,
      ∃ w : 𝓞 K, algebraMap (𝓞 K) K w = algebraMap (𝓞 K) K c * v i := by
  obtain ⟨s, rfl⟩ := hM
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K))
    (s ×ˢ (Finset.univ : Finset (Fin N))) (fun p : (Fin N → K) × Fin N => p.1 p.2)
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, ?_⟩
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    intro i
    obtain ⟨w, hw⟩ := hb (x, i) (Finset.mem_product.2 ⟨hx, Finset.mem_univ _⟩)
    exact ⟨w, by rw [← Algebra.smul_def]; exact hw⟩
  | zero => intro i; exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    intro i
    obtain ⟨w₁, h₁⟩ := hx i
    obtain ⟨w₂, h₂⟩ := hy i
    exact ⟨w₁ + w₂, by rw [map_add, h₁, h₂, Pi.add_apply, mul_add]⟩
  | smul a x _ hx =>
    intro i
    obtain ⟨w, h⟩ := hx i
    exact ⟨a * w, by rw [map_mul, h, Pi.smul_apply, Algebra.smul_def]; ring⟩

end GroundTheory.Variant₂.N1
