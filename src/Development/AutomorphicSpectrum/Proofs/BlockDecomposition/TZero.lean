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

open Finset

namespace GlobalTheory.CompanionTheory.CoefId

variable {n : ℕ}

def mon (e : Fin n → ℤ) (z : Fin n → ℂ) : ℂ := ∏ a, z a ^ e a

def dl (n : ℕ) : Fin n → ℤ := fun j => ((n - 1 - (j : ℕ) : ℕ) : ℤ)

def prs (n : ℕ) : Finset (Fin n × Fin n) := univ.filter fun p => p.1 < p.2

def score (T : Finset (Fin n × Fin n)) : Fin n → ℤ := fun c =>
  ((T.filter fun p => p.1 = c).card : ℤ) + (((prs n \ T).filter fun p => p.2 = c).card : ℤ)

def tZero (lev : Fin n → ℕ) : Finset (Fin n × Fin n) := (prs n).filter fun p => lev p.1 < lev p.2

end GlobalTheory.CompanionTheory.CoefId
