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

namespace PI.Mk

open Matrix

def TraceStep : Prop :=
  ∀ (N ℓ a : ℕ), ℓ.Prime → ∀ g : Matrix (Fin N) (Fin N) ℤ, g ^ (ℓ ^ a) = 1 →
    ∃ y : ℕ, y ≤ N / (ℓ - 1) ∧ g.trace = (N : ℤ) - (ℓ : ℤ) * (y : ℤ) ∧ (y = 0 → g = 1)

def PowerSumStep : Prop :=
  ∀ (N : ℕ) (P : Subgroup (Matrix.GeneralLinearGroup (Fin N) ℤ)) [Fintype P] (k : ℕ),
    (Fintype.card P : ℤ) ∣ ∑ g : P, (Matrix.trace ((g : Matrix.GeneralLinearGroup (Fin N) ℤ) :
      Matrix (Fin N) (Fin N) ℤ)) ^ k

def PGroupStep : Prop :=
  ∀ (N ℓ : ℕ), ℓ.Prime → ∀ P : Subgroup (Matrix.GeneralLinearGroup (Fin N) ℤ), Finite P →
    IsPGroup ℓ P → Nat.card P ∣ ℓ ^ (N / (ℓ - 1)) * (N / (ℓ - 1)).factorial

end PI.Mk
