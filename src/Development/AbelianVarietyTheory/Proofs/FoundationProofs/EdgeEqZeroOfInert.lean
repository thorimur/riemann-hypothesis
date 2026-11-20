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
import Std.Tactic.BVDecide.Normalize.Prop
open GlobalTheory.KEdge GlobalTheory.NeedB Polynomial

namespace GlobalTheory.EdgeUnr
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

theorem val_lt_one_iff (B : ValuationSubring Ω) (z : Ω) : B.valuation z < 1 ↔ z = 0 ∨ z⁻¹ ∉ B := by
  by_cases hz : z = 0
  · simp [hz]
  · simp only [hz, false_or, ← ValuationSubring.valuation_le_one_iff, map_inv₀, not_le]
    have : 0 < B.valuation z := by
      rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).mpr hz
    constructor
    · intro h; exact one_lt_inv₀ this |>.mpr h
    · intro h; exact (one_lt_inv₀ this).mp h

end GlobalTheory.EdgeUnr

namespace GlobalTheory.EdgeUnr

end GlobalTheory.EdgeUnr
