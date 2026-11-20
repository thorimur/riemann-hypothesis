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
import Std.Tactic.BVDecide.Normalize.Prop

namespace GlobalTheory.SpanPairPowSucc

theorem mem_span_pair_pow_succ {R : Type} [inst : CommRing R] (p w : R) (k : ℕ) :
    ∀ x ∈ Ideal.span {p, w} ^ (k + (1 : ℕ)),
      ∃ (c : R), ∃ G ∈ Ideal.span {p, w} ^ k, x = w ^ (k + (1 : ℕ)) * c + p * G := by
  induction k with
  | zero =>
    intro x hx
    rw [zero_add, pow_one] at hx
    obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hx
    exact ⟨b, a, by simp, by ring⟩
  | succ k ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro y hy z hz
      obtain ⟨c, G, hG, rfl⟩ := ih y hy
      obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hz
      refine ⟨c * b, w ^ (k + 1) * c * a + G * (a * p + b * w), ?_, by ring⟩
      refine Ideal.add_mem _ ?_ ?_
      · have hw : w ∈ Ideal.span ({p, w} : Set R) := Ideal.subset_span (by simp)
        exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hw _))
      · rw [pow_succ]
        exact Ideal.mul_mem_mul hG hz
    · rintro _ _ ⟨c₁, G₁, hG₁, rfl⟩ ⟨c₂, G₂, hG₂, rfl⟩
      exact ⟨c₁ + c₂, G₁ + G₂, Ideal.add_mem _ hG₁ hG₂, by ring⟩

end GlobalTheory.SpanPairPowSucc
