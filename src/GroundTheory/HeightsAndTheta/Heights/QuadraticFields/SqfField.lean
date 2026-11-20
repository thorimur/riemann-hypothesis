import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Rat.Star
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
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Rows

noncomputable section

instance sqfField_fact_noRoot (d : ℕ) [NeZero d] : Fact (∀ r : ℚ, r ^ 2 ≠ -(d : ℚ) + 0 * r) :=
  ⟨fun r h ↦ by
    have hd : (0 : ℚ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    rw [zero_mul, add_zero] at h
    nlinarith [sq_nonneg r]⟩

abbrev SqfField (d : ℕ) : Type := QuadraticAlgebra ℚ (-(d : ℚ)) 0

instance (d : ℕ) [NeZero d] : NumberField (SqfField d) := {}

instance (d : ℕ) [NeZero d] : Algebra.IsQuadraticExtension ℚ (SqfField d) :=
  ⟨QuadraticAlgebra.finrank_eq_two _ _⟩

def sqrtNegD (d : ℕ) : SqfField d := ⟨0, 1⟩

end

end GroundTheory.Heights₂.Heights.Rows
