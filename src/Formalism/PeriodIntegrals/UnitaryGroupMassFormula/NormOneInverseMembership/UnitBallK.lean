import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Sheaves.Presheaf

namespace UnitBallK

variable (K : Type*) [NormedField K] [IsUltrametricDist K]

def subring : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  zero_mem' := by simp
  one_mem' := by simp
  neg_mem' := by
    intro x hx
    simpa using hx
  add_mem' := by
    intro x y hx hy
    have key : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := IsUltrametricDist.norm_add_le_max x y
    rcases le_max_iff.1 key with h | h
    · exact le_trans h hx
    · exact le_trans h hy
  mul_mem' := by
    intro x y hx hy
    have hx' : ‖x‖ ≤ 1 := hx
    have hy' : ‖y‖ ≤ 1 := hy
    have h0x := norm_nonneg x
    have h0y := norm_nonneg y
    change ‖x * y‖ ≤ 1
    rw [norm_mul]
    nlinarith

variable {K}

theorem add_mem {x y : K} (hx : x ∈ subring K) (hy : y ∈ subring K) : x + y ∈ subring K :=
  (subring K).add_mem hx hy

theorem mul_mem {x y : K} (hx : x ∈ subring K) (hy : y ∈ subring K) : x * y ∈ subring K :=
  (subring K).mul_mem hx hy

end UnitBallK
