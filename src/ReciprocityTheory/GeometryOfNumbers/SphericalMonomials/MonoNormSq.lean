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

namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory

def sqN {N : ℕ} (z : Fin N → ℂ) : ℝ :=
  ∑ i, ‖z i‖ ^ 2

def gaussC (N : ℕ) : Measure (Fin N → ℂ) :=
  volume.withDensity fun z => ENNReal.ofReal ((Real.pi ^ N)⁻¹ * Real.exp (-sqN z))

def sphProb (N : ℕ) : Measure (Fin N → ℂ) :=
  (gaussC N).map fun z => (((Real.sqrt (sqN z))⁻¹ : ℝ) : ℂ) • z

def monoC {N : ℕ} (a : Fin N → ℕ) (z : Fin N → ℂ) : ℂ :=
  ∏ i, z i ^ a i

def monoNormSq {D : ℕ} (a : Fin (D + 1) → ℕ) : ℝ :=
  ((∏ i, (a i).factorial : ℕ) : ℝ) * (D.factorial : ℝ) / (((∑ i, a i) + D).factorial : ℝ)

def chiP (D n : ℕ) : ℝ :=
  -(1 / 2) * ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, Real.log (monoNormSq a)

end ReciprocityTheory.GeometryOfNumbersTheory
