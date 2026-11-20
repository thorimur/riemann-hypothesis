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

namespace Formalism.L2.S.S7.PositiveOrthantChangeOfVariables

open MeasureTheory Set
open scoped ENNReal

def posO (a : ℕ) : Set (Fin a → ℝ) := Set.univ.pi fun _ => Set.Ioi (0 : ℝ)

def chv {a : ℕ} (e : Fin a → ℝ) (t : Fin a → ℝ) : Fin a → ℝ := fun i => t i ^ (-(e i)⁻¹)

def chvD {a : ℕ} (e : Fin a → ℝ) (t : Fin a → ℝ) : (Fin a → ℝ) →L[ℝ] (Fin a → ℝ) :=
  ContinuousLinearMap.pi fun i => ((-(e i)⁻¹) * t i ^ (-(e i)⁻¹ - 1)) • ContinuousLinearMap.proj i

end Formalism.L2.S.S7.PositiveOrthantChangeOfVariables

end
