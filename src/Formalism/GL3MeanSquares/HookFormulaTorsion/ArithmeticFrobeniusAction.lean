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
import Mathlib.RingTheory.WittVector.Frobenius
import Mathlib.RingTheory.WittVector.Teichmuller
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

namespace Formalism.HermitianLattices.IntegralLatticeDensity

open Finset

private theorem frob_teich (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] [CharP k p] (x : k) :
    WittVector.frobenius (WittVector.teichmuller p x) = (WittVector.teichmuller p x) ^ p := by
  rw [← map_pow]
  ext n
  rw [WittVector.coeff_frobenius_charP]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero]
  · rw [WittVector.teichmuller_coeff_pos p _ n hn, WittVector.teichmuller_coeff_pos p _ n hn,
      zero_pow (Fact.out : p.Prime).ne_zero]

end Formalism.HermitianLattices.IntegralLatticeDensity
