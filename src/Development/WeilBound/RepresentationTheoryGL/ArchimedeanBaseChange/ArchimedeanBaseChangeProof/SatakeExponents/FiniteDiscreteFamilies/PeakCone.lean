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

namespace PositivityTheory.Rg.BcB.F.F5

def coneGL (n : ℕ) (M : ℤ) : Set (Fin n → ℤ) := {x | ∀ i j : Fin n, i < j → x j + M ≤ x i}

def evalGL {n : ℕ} (c : (Fin n → ℤ) →₀ ℂ) (ξ : Fin n → ℂˣ) : ℂ :=
  c.sum fun x a => a * ((∏ i, ξ i ^ x i : ℂˣ) : ℂ)

def PeakCone : Prop := ∀ (n : ℕ) (M : ℤ) (α : Fin n → ℂˣ) (S : Finset (Fin n → ℂˣ)), α ∉ S →
  ∃ c : (Fin n → ℤ) →₀ ℂ, (↑c.support ⊆ coneGL n M) ∧ evalGL c α = 1 ∧ ∀ β ∈ S, evalGL c β = 0

end PositivityTheory.Rg.BcB.F.F5

end
