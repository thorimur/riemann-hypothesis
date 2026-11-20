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

namespace PositivityTheory.RgHe.Frame

variable {m : ℕ}

def pfR (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ) (j : Fin m) : ℝ :=
  (∏ i, (d' j - d i)) / ∏ k ∈ univ.erase j, (d' j - d' k)

def pfX (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ) : ℝ := ∑ i, d i - ∑ j, d' j

def above (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ) (r : ℝ) : ℕ :=
  (univ.filter fun x : Fin (m + 1) ⊕ Fin m => r < Sum.elim d d' x).card

def pfD (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ) (i : Fin (m + 1)) : ℝ :=
  (∏ k ∈ univ.erase i, (d i - d k)) / ∏ j, (d i - d' j)

end PositivityTheory.RgHe.Frame
