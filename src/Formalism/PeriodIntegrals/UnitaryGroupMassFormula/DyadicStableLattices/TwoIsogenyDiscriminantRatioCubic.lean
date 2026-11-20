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
open Filter Topology
open scoped ComplexConjugate

namespace PI.GoodTwo
namespace IsogenyReduction

lemma alg (e g2 g3 : ℂ) (h : g3 = 4 * e ^ 3 - g2 * e) (hd : g2 ^ 3 - 27 * g3 ^ 2 ≠ 0) :
    ((60 * e ^ 2 - 4 * g2) ^ 3 - 27 * (g3 + 84 * e ^ 3 - 7 * g2 * e) ^ 2
      + 16 * (g2 ^ 3 - 27 * g3 ^ 2)) ^ 3 =
    1728 * g2 ^ 3 / (g2 ^ 3 - 27 * g3 ^ 2) *
      ((60 * e ^ 2 - 4 * g2) ^ 3 - 27 * (g3 + 84 * e ^ 3 - 7 * g2 * e) ^ 2) *
      (g2 ^ 3 - 27 * g3 ^ 2) ^ 2 := by
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff hd]
  subst h
  ring

end IsogenyReduction

open IsogenyReduction

end PI.GoodTwo
