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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Monotonicity.Lemmas
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
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem exists_unit_at_prime_mul_integral (K : Type) [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K)) (T : Set K) (d : 𝓞 K) (hd : d ≠ 0)
    (hdT : ∀ t ∈ T, IsIntegral ℤ ((d : K) * t)) (hPT : ∀ t ∈ T, P.valuation K t ≤ 1) :
    ∃ s : 𝓞 K, P.valuation K (s : K) = 1 ∧ ∀ t ∈ T, IsIntegral ℤ ((s : K) * t) := by
  have hspan : Ideal.span {d} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hd
  have hirr : Irreducible P.asIdeal := (Ideal.prime_of_isPrime P.ne_bot P.isPrime).irreducible
  obtain ⟨a, J, hPJ, hdJ⟩ := WfDvdMonoid.max_power_factor hspan hirr
  have hJP : ¬ J ≤ P.asIdeal := fun h => hPJ (Ideal.dvd_iff_le.mpr h)
  obtain ⟨s, hsJ, hsP⟩ := Set.not_subset.mp hJP
  have hsJ' : J ∣ Ideal.span {s} := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hsJ)
  have hvPs : P.valuation K (s : K) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    refine le_antisymm (P.intValuation_le_one s) (not_lt.mp fun h => hsP ?_)
    rw [HeightOneSpectrum.intValuation_lt_one_iff_dvd, Ideal.dvd_span_singleton] at h
    exact h

  have hQ : ∀ Q : HeightOneSpectrum (𝓞 K), Q ≠ P → Q.intValuation s ≤ Q.intValuation d := by
    intro Q hQP
    have hQd : Q.intValuation d = WithZero.exp (-((Associates.mk Q.asIdeal).count
        (Associates.mk (Ideal.span {d})).factors : ℤ)) := by
      rw [HeightOneSpectrum.intValuation_def, if_neg hd]
    set n := (Associates.mk Q.asIdeal).count (Associates.mk (Ideal.span {d})).factors
    have hdiv : Q.asIdeal ^ n ∣ Ideal.span {d} :=
      (Q.intValuation_le_pow_iff_dvd d n).mp (le_of_eq hQd)
    have hne : Q.asIdeal ≠ P.asIdeal := fun h => hQP (HeightOneSpectrum.ext h)
    have hcop : IsCoprime Q.asIdeal P.asIdeal :=
      Ideal.isCoprime_iff_sup_eq.mpr (Ideal.IsMaximal.coprime_of_ne Q.isMaximal P.isMaximal hne)
    have hcopn : IsCoprime (Q.asIdeal ^ n) (P.asIdeal ^ a) := hcop.pow
    rw [hdJ] at hdiv
    have hQJ : Q.asIdeal ^ n ∣ J := hcopn.dvd_of_dvd_mul_left hdiv
    rw [hQd]
    exact (Q.intValuation_le_pow_iff_dvd s n).mpr (hQJ.trans hsJ')
  refine ⟨s, hvPs, fun t ht => ?_⟩
  have hdt : (d : K) * t ∈ (algebraMap (𝓞 K) K).range := ⟨⟨_, hdT t ht⟩, rfl⟩
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K ((s : K) * t) (by
    intro Q
    by_cases hQP : Q = P
    · subst hQP
      rw [map_mul, hvPs, one_mul]; exact hPT t ht
    · obtain ⟨z, hz⟩ := hdt
      have h1 : Q.valuation K ((d : K) * t) ≤ 1 := by
        rw [← hz]; exact Q.valuation_le_one z
      rw [map_mul] at h1 ⊢
      calc Q.valuation K (s : K) * Q.valuation K t ≤ Q.valuation K (d : K) * Q.valuation K t := by
            gcongr
            rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
            exact hQ Q hQP
        _ ≤ 1 := h1)
  rw [← hy]
  exact RingOfIntegers.isIntegral_coe y

end GlobalTheory
