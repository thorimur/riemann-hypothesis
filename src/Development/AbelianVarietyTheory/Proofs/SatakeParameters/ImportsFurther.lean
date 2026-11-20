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

namespace GlobalTheory.NatMulIsIntegralSatakeParameters

theorem exists_nat_mul_isIntegral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * a) := by
  obtain ⟨y, hy0, hy'⟩ := exists_integral_multiples ℤ ℚ (L := E) {a}
  have hy := hy' a (Finset.mem_singleton_self a)
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, ?_⟩
  rw [zsmul_eq_mul] at hy
  rcases Int.natAbs_eq y with h | h
  · rw [h] at hy
    simpa using hy
  · rw [h] at hy
    simpa using hy.neg

theorem exists_nsmul_mem {E : Type} [Field E] [NumberField E] {N : ℕ}
    (Lb : Submodule (NumberField.RingOfIntegers E) (Fin N → E)) {v : Fin N → E}
    (hv : v ∈ Submodule.span E (↑Lb : Set (Fin N → E))) :
    ∃ n : ℕ, 0 < n ∧ n • v ∈ Lb := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n₁, hn₁, h₁⟩ := hx
    obtain ⟨n₂, hn₂, h₂⟩ := hy
    refine ⟨n₁ * n₂, Nat.mul_pos hn₁ hn₂, ?_⟩
    have e : (n₁ * n₂) • (x + y) = n₂ • (n₁ • x) + n₁ • (n₂ • y) := by
      ext i
      show (n₁ * n₂) • (x i + y i) = n₂ • (n₁ • x i) + n₁ • (n₂ • y i)
      simp only [nsmul_eq_mul, Nat.cast_mul]
      ring
    rw [e]
    exact Lb.add_mem (nsmul_mem h₁ n₂) (nsmul_mem h₂ n₁)
  | smul c x _ hx =>
    obtain ⟨n, hn, h⟩ := hx
    obtain ⟨m, hm, hc⟩ := exists_nat_mul_isIntegral c
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    have e : (m * n) • (c • x) =
        (⟨(m : E) * c, (mem_integralClosure_iff ℤ E).mpr hc⟩ : NumberField.RingOfIntegers E) • (n • x) := by
      ext i
      show (m * n) • (c * x i) = ((m : E) * c) * (n • x i)
      simp only [nsmul_eq_mul, Nat.cast_mul]
      ring
    rw [e]
    exact Lb.smul_mem _ h

end GlobalTheory.NatMulIsIntegralSatakeParameters
