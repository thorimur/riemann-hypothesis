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

namespace GlobalTheory.InterpCurv

def logisticFactor (κ L u : ℝ) : ℝ := 1 / (1 + Real.exp (κ * (u - L)))

def weightProfile (χ : ℝ → ℝ) (κ L t u : ℝ) : ℝ :=
  t * (χ (u / L) / (1 + Real.exp (κ * (u - L))))

theorem weightProfile_eq (χ : ℝ → ℝ) (κ L t u : ℝ) :
    weightProfile χ κ L t u = t * (χ (u / L) * logisticFactor κ L u) := by
  rw [weightProfile, logisticFactor, mul_one_div]

theorem logisticFactor_mem (κ L u : ℝ) :
    0 < logisticFactor κ L u ∧ logisticFactor κ L u < 1 := by
  have h := Real.exp_pos (κ * (u - L))
  refine ⟨by unfold logisticFactor; positivity, ?_⟩
  rw [logisticFactor, div_lt_one (by positivity)]
  linarith

end GlobalTheory.InterpCurv
