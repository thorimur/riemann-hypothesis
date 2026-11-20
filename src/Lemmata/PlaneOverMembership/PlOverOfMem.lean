import Formalism.LocalToGlobal.ExponentGrids.ScaledCoordinatesValuationLemma
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat

namespace Bl.PlaneOverMembership

open NumberField IsDedekindDomain

private theorem plOver_of_mem {K : Type} [Field K] [NumberField K] {g : ℕ} (hg : 0 < g)
    (w : HeightOneSpectrum (𝓞 K)) (h : (g : 𝓞 K) ∈ w.asIdeal) : Formalism.DivisionValues.PlOver g w := by
  classical
  have hc : ((g : 𝓞 K) : K) = (g : K) := by simp
  have hg0 : (g : 𝓞 K) ≠ 0 := by exact_mod_cast hg.ne'
  have hJ : (Ideal.span {(g : 𝓞 K)} : Ideal (𝓞 K)) ≠ 0 := by
    rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  have hm : Associates.mk (Ideal.span {(g : 𝓞 K)}) ≠ 0 := by rwa [ne_eq, Associates.mk_eq_zero]
  have h1 : 1 ≤ (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {(g : 𝓞 K)})).factors := by
    rw [← Associates.prime_pow_dvd_iff_le hm w.associates_irreducible, pow_one,
      Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact h
  unfold Formalism.DivisionValues.PlOver Formalism.DivisionValues.vw
  rw [← hc, ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K _ hJ]
  exact_mod_cast h1

theorem goal1 :
  Formalism.AtG.FinitePlaceLiesOverPrime := by
  intro K _ _
  refine ⟨fun w => Ideal.absNorm (Ideal.under ℤ w.asIdeal), fun w => ?_⟩
  have : NeZero w.asIdeal := ⟨w.ne_bot⟩
  have hp : (Ideal.absNorm (Ideal.under ℤ w.asIdeal)).Prime := Nat.absNorm_under_prime w.asIdeal
  exact ⟨hp, plOver_of_mem hp.pos w (Int.absNorm_under_mem w.asIdeal)⟩

end Bl.PlaneOverMembership
