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

noncomputable section

namespace PI.PrimesDyadicRS.W

def At (y : ℝ) : Prop :=
  3 * y / (5 * Real.log y) < (Nat.primeCounting ⌊2 * y⌋₊ : ℝ) - (Nat.primeCounting ⌊y⌋₊ : ℝ)

def SmallNat : Prop := ∀ h : ℕ, 41 ≤ h → h < 131072 →
  3 * ((h : ℝ) + 1) <
    10 * ((Nat.primeCounting h : ℝ) - (Nat.primeCounting (h / 2) : ℝ)) * Real.log ((h : ℝ) / 2)

def ThetaDiff : Prop := ∀ y : ℝ, 1 ≤ y →
  Chebyshev.theta (2 * y) - Chebyshev.theta y ≤
    ((Nat.primeCounting ⌊2 * y⌋₊ : ℝ) - (Nat.primeCounting ⌊y⌋₊ : ℝ)) * Real.log (2 * y)

def PsiTheta : Prop := ∀ x : ℝ, 1 ≤ x →
  Chebyshev.psi x - Chebyshev.theta x ≤ 3 * Chebyshev.psi (Real.sqrt x)

def RealIneq : Prop := ∀ y : ℝ, 65536 ≤ y →
  3 * y / (5 * Real.log y) * Real.log (2 * y) <
    (0.92129 * (2 * y) - 5 / 2 * Real.log (2 * y))
      - 3 * (1.1056 * Real.sqrt (2 * y) + 0.7 * Real.log (Real.sqrt (2 * y)) ^ 2)
      - (1.1056 * y + 0.7 * Real.log y ^ 2)

end PI.PrimesDyadicRS.W
