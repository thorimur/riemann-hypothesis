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

theorem UpperTheory.Reformulated.B.Yia3.main :
    ∀ (r : ℝ), (0 : ℝ) < r → ∀ (k : ℕ), (↑(r ^ (2 : ℕ)) : ℂ) ^ ((↑k : ℂ) / (2 : ℂ)) = (↑r : ℂ) ^ k := by
  intro r hr k
  have hr2 : (0 : ℝ) ≤ r ^ (2 : ℕ) := by positivity
  have hcast : ((↑k : ℂ) / (2 : ℂ)) = (((k : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, ← Complex.ofReal_cpow hr2]
  have hreal : (r ^ (2 : ℕ)) ^ ((k : ℝ) / 2) = r ^ k := by
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
    have : ((2 : ℕ) : ℝ) * ((k : ℝ) / 2) = (k : ℝ) := by push_cast; ring
    rw [this, Real.rpow_natCast]
  rw [hreal]
  push_cast
  rfl
