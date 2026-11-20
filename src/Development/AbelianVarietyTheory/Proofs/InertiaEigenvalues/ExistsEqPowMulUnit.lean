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

namespace GlobalTheory.PowMulUnit

theorem exists_eq_pow_mul_unit {S : Type} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    {π : S} (hπ : IsLocalRing.maximalIdeal S = Ideal.span {π}) {x : S} (hx : x ≠ (0 : S)) :
    ∃ (k : ℕ) (u : S), IsUnit u ∧ x = π ^ k * u := by
  classical
  have hK := Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal S)
    (IsLocalRing.maximalIdeal.isMaximal S).ne_top
  have hex : ∃ n : ℕ, ¬ (π ^ n ∣ x) := by
    by_contra h0
    have h : ∀ n : ℕ, π ^ n ∣ x := fun n => not_not.mp (not_exists.mp h0 n)
    apply hx
    have hmem : x ∈ ⨅ n : ℕ, IsLocalRing.maximalIdeal S ^ n := by
      refine Ideal.mem_iInf.mpr fun n => ?_
      rw [hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact h n
    rw [hK] at hmem
    exact hmem
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    have h1 := Nat.find_spec hex
    rw [h0, pow_zero] at h1
    exact h1 (one_dvd x)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hdk : π ^ k ∣ x := by
    have := Nat.find_min hex (show k < Nat.find hex by omega)
    exact not_not.mp this
  obtain ⟨u, rfl⟩ := hdk
  refine ⟨k, u, ?_, rfl⟩
  by_contra hu
  have hum : u ∈ IsLocalRing.maximalIdeal S := (IsLocalRing.mem_maximalIdeal u).mpr hu
  rw [hπ, Ideal.mem_span_singleton] at hum
  obtain ⟨w, rfl⟩ := hum
  apply Nat.find_spec hex
  rw [hk, pow_succ]
  exact ⟨w, by ring⟩

end GlobalTheory.PowMulUnit
