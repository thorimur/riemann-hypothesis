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

namespace GlobalTheory.CompanionTheory.WeilSiegel.Inf0

open scoped Matrix

variable {P ι : Type}

def qR0 [Fintype ι] (A : P → Matrix ι ι ℝ) (x : P → ι → ℝ) : P → ℝ :=
  fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (A w *ᵥ x w))

def gaussR [Fintype P] [Fintype ι] (Pm : P → Matrix ι ι ℝ) (x : P → ι → ℝ) : ℝ :=
  Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w))

def boxR [Fintype ι] (t : P → ℝ) : Set (P → ι → ℝ) :=
  {x | ∀ w, ‖x w‖ ≤ t w}

def coreR [Fintype ι] (δ R : ℝ) : Set (P → ι → ℝ) :=
  {x | ∀ w, δ ≤ ‖x w‖ ∧ ‖x w‖ ≤ R}

end GlobalTheory.CompanionTheory.WeilSiegel.Inf0
