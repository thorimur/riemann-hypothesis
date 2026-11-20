import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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

namespace Formalism.InvariantFactorPaths.MC

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.InvariantFactorPaths.OddLevelGainBounds Formalism.InvariantFactorPaths.OddLevelGainBounds.TB Formalism.InvariantFactorPaths.PW Formalism.InvariantFactorPaths.L4 MvPolynomial Finset

theorem kap_num (N s : ℕ) (Q : ℝ) (hQ : 0 ≤ Q) (hN : N ≤ 2 * s + 2) :
    (3 / 2 : ℝ) * (((N : ℝ) + 2) * Q) ≤ 3 * ((s : ℝ) + 2) * Q := by
  have h : (N : ℝ) ≤ 2 * (s : ℝ) + 2 := by exact_mod_cast hN
  nlinarith

end Formalism.InvariantFactorPaths.MC
