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
import Mathlib.Tactic.ENatToNat
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

open IsDedekindDomain FractionalIdeal
open scoped nonZeroDivisors

namespace GlobalTheory.AdicValuationCountFactors

variable {R : Type*} {K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

theorem valuation_algebraMap_eq_count {r : R} (hr : r ≠ 0) :
    v.valuation K (algebraMap R K r) =
      WithZero.exp (-FractionalIdeal.count K v (spanSingleton R⁰ (algebraMap R K r))) := by
  have hJ : Ideal.span {r} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hr
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg v hr,
    ← coeIdeal_span_singleton, count_coe K v hJ]

theorem valuation_eq_exp_neg_count {x : K} (hx : x ≠ 0) :
    v.valuation K x = WithZero.exp (-FractionalIdeal.count K v (spanSingleton R⁰ x)) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hx
  have hbK : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have haK : algebraMap R K a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 ha0
  have hs : spanSingleton R⁰ (algebraMap R K a / algebraMap R K b) =
      spanSingleton R⁰ (algebraMap R K a) * (spanSingleton R⁰ (algebraMap R K b))⁻¹ := by
    rw [div_eq_mul_inv, ← spanSingleton_mul_spanSingleton, spanSingleton_inv]
  rw [hs, count_mul K v (spanSingleton_ne_zero_iff.2 haK) (inv_ne_zero (spanSingleton_ne_zero_iff.2 hbK)),
    count_inv, map_div₀, valuation_algebraMap_eq_count (K := K) v ha0,
    valuation_algebraMap_eq_count (K := K) v hb0, ← WithZero.exp_sub]
  congr 1
  ring

end GlobalTheory.AdicValuationCountFactors
