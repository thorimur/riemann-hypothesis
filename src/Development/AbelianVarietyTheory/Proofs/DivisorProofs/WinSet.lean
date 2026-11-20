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

open MvPolynomial GlobalTheory.FlagPoly GlobalTheory.FlagForm

noncomputable section

namespace GlobalTheory.FlagCurve

def winSet (ι : Type) [Fintype ι] (N j : ℕ) : Finset (ι × Fin N × Fin N) :=
  Finset.univ.filter fun p => p.2.1 < p.2.2 ∧ ((p.2.2 : ℕ) < j ∨ j ≤ (p.2.1 : ℕ))

def crSet (ι : Type) [Fintype ι] (N j : ℕ) : Finset (ι × Fin N × Fin N) :=
  Finset.univ.filter fun p => p.2.1 < p.2.2 ∧ (p.2.1 : ℕ) < j ∧ j ≤ (p.2.2 : ℕ)

def mono {σ : Type} [DecidableEq σ] (R : Finset σ) : σ →₀ ℕ := ∑ s ∈ R, Finsupp.single s 1

end GlobalTheory.FlagCurve
