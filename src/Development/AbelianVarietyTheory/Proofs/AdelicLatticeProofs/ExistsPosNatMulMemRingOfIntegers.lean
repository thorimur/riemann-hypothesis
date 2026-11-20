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
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace GlobalTheory.NatMultipleRingOfIntegers

theorem exists_pos_nat_mul_mem_ringOfIntegers {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ m : ℕ, 0 < m ∧ ∃ b : NumberField.RingOfIntegers E, (b : E) = (m : E) * a := by
  have h1 : IsAlgebraic ℚ a := Algebra.IsAlgebraic.isAlgebraic a
  have h2 : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr h1
  obtain ⟨y, hy, hint⟩ := h2.exists_integral_multiple
  have hint' : IsIntegral ℤ ((y : E) * a) := by
    simpa [zsmul_eq_mul] using hint
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  have hm : IsIntegral ℤ ((y.natAbs : E) * a) := by
    rcases Int.natAbs_eq y with h | h
    · have e : ((y.natAbs : ℕ) : E) = (y : E) := by
        conv_rhs => rw [h]
        exact (Int.cast_natCast _).symm
      rw [e]; exact hint'
    · have e : ((y.natAbs : ℕ) : E) = -(y : E) := by
        conv_rhs => rw [h]
        rw [Int.cast_neg, neg_neg, Int.cast_natCast]
      rw [e, neg_mul]; exact hint'.neg
  exact ⟨⟨_, hm⟩, rfl⟩

end GlobalTheory.NatMultipleRingOfIntegers
