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

open ReciprocityTheory.Ty.Fin

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.ColStep

def colGe (d j : ℕ) (i l : Fin d) : Prop := i < l ∧ j ≤ (l : ℕ)

variable (K : Type) [Field K]

def colGeE (d j : ℕ) (i l : Fin d) : K := if (l : ℕ) = i + 1 ∧ j ≤ (l : ℕ) then 1 else 0

def colGeR (d j : ℕ) (r : Fin j → K) (i l : Fin d) : K :=
  colGeE K d (j + 1) i l + if h : (l : ℕ) = j ∧ (i : ℕ) < j then r ⟨i, h.2⟩ else 0

def blkEmb (d j : ℕ) (A : Matrix (Fin j) (Fin j) K) : Matrix (Fin d) (Fin d) K := fun i l =>
  if h : (i : ℕ) < j ∧ (l : ℕ) < j then A ⟨i, h.1⟩ ⟨l, h.2⟩ else if i = l then 1 else 0

end GlobalTheory.CompanionTheory.TyFin.ColStep
