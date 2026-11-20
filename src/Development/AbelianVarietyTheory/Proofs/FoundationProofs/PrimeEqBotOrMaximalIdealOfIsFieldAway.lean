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
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
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

namespace GlobalTheory

open IsLocalRing

section

variable {B : Type*} [CommRing B] [IsDomain B]

variable [IsNoetherianRing B] [IsLocalRing B]

theorem prime_eq_bot_or_maximalIdeal_of_forall_mem {f : B} (hf : f ≠ 0)
    (H : ∀ p : Ideal B, p.IsPrime → p ≠ ⊥ → f ∈ p) {p : Ideal B} (hp : p.IsPrime) :
    p = ⊥ ∨ p = maximalIdeal B := by
  classical
  refine or_iff_not_imp_left.mpr fun hp0 => ?_
  have hfin := (Ideal.span {f}).finite_minimalPrimes_of_isNoetherianRing
  have hmin : ∀ q : Ideal B, q.IsPrime → q ≠ ⊥ →
      ∃ P ∈ (Ideal.span {f}).minimalPrimes, P ≤ q := fun q hq hq0 =>
    Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem q).mpr (H q hq hq0))

  have hcover : ((maximalIdeal B : Ideal B) : Set B) ⊆
      ⋃ P ∈ (hfin.toFinset : Set (Ideal B)), ((id P : Ideal B) : Set B) := by
    intro x hx
    simp only [Set.Finite.coe_toFinset, id, Set.mem_iUnion, SetLike.mem_coe, exists_prop]
    by_cases hx0 : x = 0
    · obtain ⟨P, hP, -⟩ := hmin p hp hp0
      exact ⟨P, hP, hx0 ▸ P.zero_mem⟩
    obtain ⟨Q, hQ, -⟩ := Ideal.exists_minimalPrimes_le
      ((Ideal.span_singleton_le_iff_mem (maximalIdeal B)).mpr hx)
    haveI hQp : Q.IsPrime := hQ.1.1
    have hxQ : x ∈ Q := (Ideal.span_singleton_le_iff_mem Q).mp hQ.1.2
    have hQ0 : Q ≠ ⊥ := fun h => hx0 (by simpa [h] using hxQ)
    have hQ1 : Q.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ Q hQ
    obtain ⟨P, hP, hPQ⟩ := hmin Q hQp hQ0
    haveI hPp : P.IsPrime := hP.1.1
    have hfP : f ∈ P := (Ideal.span_singleton_le_iff_mem P).mp hP.1.2
    refine ⟨P, hP, ?_⟩
    rcases hPQ.eq_or_lt with h | h
    · exact h ▸ hxQ
    · have h1 : P.height < 1 := (Ideal.height_strict_mono_of_isPrime h).trans_le hQ1
      rw [ENat.lt_one_iff_eq_zero, Ideal.height_eq_zero_iff_eq_bot] at h1
      exact absurd (by simpa [h1] using hfP) hf
  obtain ⟨P, hP, hmP⟩ := (Ideal.subset_union_prime (⊥ : Ideal B) ⊥ fun P hP _ _ =>
    ((Set.Finite.mem_toFinset hfin).mp hP).1.1).mp hcover
  have hP' := (Set.Finite.mem_toFinset hfin).mp hP
  have hpm : p ≤ maximalIdeal B := le_maximalIdeal hp.ne_top
  exact le_antisymm hpm (hmP.trans (hP'.2
    ⟨hp, (Ideal.span_singleton_le_iff_mem p).mpr (H p hp hp0)⟩ (hpm.trans hmP)))

end

end GlobalTheory
