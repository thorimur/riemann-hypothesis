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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.MvPowerSeries.Order
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
import Mathlib.Topology.Sheaves.Presheaf
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.DivMono

theorem coeff_finsuppProd_eq_zero_of_degree_lt :
    ∀ (R : Type) [CommRing R] (σ τ : Type) (u : τ → MvPowerSeries σ R), (∀ j, constantCoeff (u j) = 0) →
      ∀ (α : τ →₀ ℕ) (β : σ →₀ ℕ), β.degree < α.degree → coeff β (α.prod fun j e => u j ^ e) = 0 := by
  intro R _ σ τ u hu α β hβ
  apply coeff_of_lt_order
  have hle : ((α.degree : ℕ) : ℕ∞) ≤ (α.prod fun j e => u j ^ e).order := by
    unfold Finsupp.prod
    refine le_trans ?_ (le_order_prod (fun j => u j ^ α j) α.support)
    rw [Finsupp.degree_apply, Nat.cast_sum]
    exact Finset.sum_le_sum fun j _ => le_order_pow_of_constantCoeff_eq_zero (α j) (hu j)
  exact lt_of_lt_of_le (by exact_mod_cast hβ) hle

end GlobalTheory.DivMono
