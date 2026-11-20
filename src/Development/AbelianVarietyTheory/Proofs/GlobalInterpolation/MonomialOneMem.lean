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
import Mathlib.RingTheory.MvPowerSeries.Inverse
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
namespace GlobalTheory.PowerSeriesMaximalBound
open MvPowerSeries

variable {O : Type} [CommRing O] [IsLocalRing O] {a : ℕ}

lemma C_mem_max {r : O} (hr : r ∈ IsLocalRing.maximalIdeal O) :
    (C r : MvPowerSeries (Fin a) O) ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff, constantCoeff_C]
  exact hr

lemma X_mem_max (i : Fin a) :
    (X i : MvPowerSeries (Fin a) O) ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff, constantCoeff_X]
  exact not_isUnit_zero

lemma map_le_max :
    Ideal.map (C : O →+* MvPowerSeries (Fin a) O) (IsLocalRing.maximalIdeal O)
      ≤ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  exact C_mem_max hr

lemma monomial_one_mem (v : Fin a →₀ ℕ) :
    (monomial v (1 : O)) ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ^ (Finsupp.degree v) := by
  induction v using Finsupp.induction with
  | zero => simp
  | single_add i k w hi hk ih =>
    rw [← one_mul (1 : O), ← monomial_mul_monomial, map_add, Finsupp.degree_single, pow_add, ← X_pow_eq]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (X_mem_max i) k) ih

theorem main : ∀ {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O] {a N : ℕ} (v : Fin a →₀ ℕ) {c : O}, c ∈ IsLocalRing.maximalIdeal O ^ (N - (Finsupp.degree : (Fin a →₀ ℕ) → ℕ) v) → (MvPowerSeries.monomial v : O → MvPowerSeries (Fin a) O) c ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ^ N := by
  intro O _ _ a N v c hc
  have h1 : (C c : MvPowerSeries (Fin a) O) ∈
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ^ (N - Finsupp.degree v) := by
    have : (C c : MvPowerSeries (Fin a) O) ∈
        Ideal.map (C : O →+* MvPowerSeries (Fin a) O) (IsLocalRing.maximalIdeal O ^ (N - Finsupp.degree v)) :=
      Ideal.mem_map_of_mem _ hc
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono map_le_max _ this
  have h2 : monomial v c = C c * monomial v (1 : O) := by
    rw [← monomial_zero_eq_C, monomial_mul_monomial, zero_add, mul_one]
  rw [h2]
  refine Ideal.pow_le_pow_right (by omega : N ≤ (N - Finsupp.degree v) + Finsupp.degree v) ?_
  rw [pow_add]
  exact Ideal.mul_mem_mul h1 (monomial_one_mem v)

end GlobalTheory.PowerSeriesMaximalBound
