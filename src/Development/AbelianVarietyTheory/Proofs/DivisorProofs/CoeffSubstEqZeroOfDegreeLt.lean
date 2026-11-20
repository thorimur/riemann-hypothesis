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
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory

theorem coeff_subst_eq_zero_of_degree_lt :
    ∀ (R : Type) [CommRing R] (σ τ : Type) [Fintype σ] (u : σ → MvPowerSeries τ R)
      (f : MvPowerSeries σ R) (M : ℕ), (∀ i, constantCoeff (u i) = 0) →
      (∀ α : σ →₀ ℕ, α.degree < M → coeff α f = 0) →
      ∀ β : τ →₀ ℕ, β.degree < M → coeff β (subst u f) = 0 := by
  intro R _ σ τ _ u f M hu hf β hβ
  have hs : HasSubst u := ⟨fun i => by rw [hu i]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
  rw [coeff_subst hs]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hd : d.degree < M
  · simp [hf d hd]
  · push_neg at hd
    have hord : ((d.degree : ℕ) : ℕ∞) ≤ (d.prod fun s e => u s ^ e).order := by
      unfold Finsupp.prod
      refine le_trans ?_ (le_order_prod (fun s => u s ^ d s) d.support)
      have hdeg : d.degree = ∑ i ∈ d.support, d i := rfl
      rw [hdeg, Nat.cast_sum]
      exact Finset.sum_le_sum fun s _ => le_order_pow_of_constantCoeff_eq_zero (d s) (hu s)
    have h0 : coeff β (d.prod fun s e => u s ^ e) = 0 := by
      apply coeff_of_lt_order
      exact lt_of_lt_of_le (by exact_mod_cast (lt_of_lt_of_le hβ hd)) hord
    rw [h0, smul_zero]

end GlobalTheory
