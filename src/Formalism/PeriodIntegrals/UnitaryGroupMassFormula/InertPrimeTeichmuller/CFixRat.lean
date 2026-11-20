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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

open NumberField

noncomputable section

namespace PI.OkpW

variable {K : Type} [Field K] [NumberField K]

theorem c_invol (hK : Module.finrank ℚ K = 2) (c : K →+* K) (x : K) : c (c x) = x := by
  let f : K →ₐ[ℚ] K := c.toRatAlgHom
  let e : K ≃ₐ[ℚ] K := AlgEquiv.ofBijective f (AlgHom.bijective f)
  have hcard : Nat.card (K ≃ₐ[ℚ] K) ≤ 2 := by
    rw [← hK, Nat.card_congr (algEquivEquivAlgHom ℚ K).toEquiv]
    exact card_algHom_le_finrank ℚ K K
  have hpos : 0 < Nat.card (K ≃ₐ[ℚ] K) := Nat.card_pos
  have h1 : e ^ Nat.card (K ≃ₐ[ℚ] K) = 1 := pow_card_eq_one'
  have he : e ^ 2 = 1 := by
    rcases (by omega : Nat.card (K ≃ₐ[ℚ] K) = 1 ∨ Nat.card (K ≃ₐ[ℚ] K) = 2) with h | h
    · rw [h, pow_one] at h1; rw [h1, one_pow]
    · rwa [h] at h1
  have := DFunLike.congr_fun he x
  rw [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply] at this
  exact this

theorem c_fix_rat (hK : Module.finrank ℚ K = 2) (c : K →+* K) (hc : ∃ x, c x ≠ x) {y : K}
    (hy : c y = y) : ∃ r : ℚ, (r : K) = y := by
  let D : K →ₗ[ℚ] K := c.toRatAlgHom.toLinearMap - LinearMap.id
  have hD : ∀ z, D z = c z - z := fun z => rfl
  have hS : LinearMap.ker D ≠ ⊤ := by
    obtain ⟨x, hx⟩ := hc
    intro h
    have hm : x ∈ LinearMap.ker D := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hD, sub_eq_zero] at hm
    exact hx hm
  have hlt : Module.finrank ℚ (LinearMap.ker D) < 2 :=
    hK ▸ Submodule.finrank_lt hS
  have hle : (ℚ ∙ (1 : K)) ≤ LinearMap.ker D := by
    rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, hD, map_one, sub_self]
  have heq : (ℚ ∙ (1 : K)) = LinearMap.ker D :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [finrank_span_singleton one_ne_zero]; omega)
  have hyS : y ∈ LinearMap.ker D := by rw [LinearMap.mem_ker, hD, hy, sub_self]
  rw [← heq, Submodule.mem_span_singleton] at hyS
  obtain ⟨r, hr⟩ := hyS
  exact ⟨r, by rw [← hr, Rat.smul_def, mul_one]⟩

theorem add_c_int (hK : Module.finrank ℚ K = 2) (c : K →+* K) (hc : ∃ x, c x ≠ x) (a : 𝓞 K) :
    ∃ n : ℤ, a + RingOfIntegers.mapRingHom c a = (n : 𝓞 K) := by
  have hfix : c ((a : K) + c a) = (a : K) + c a := by rw [map_add, c_invol hK c, add_comm]
  obtain ⟨r, hr⟩ := c_fix_rat hK c hc hfix
  have hint : IsIntegral ℤ (algebraMap ℚ K r) := by
    rw [eq_ratCast, hr]
    have := (a + RingOfIntegers.mapRingHom c a).isIntegral_coe
    simpa [RingOfIntegers.mapRingHom_apply] using this
  rw [isIntegral_algebraMap_iff (algebraMap ℚ K).injective,
    IsIntegrallyClosed.isIntegral_iff] at hint
  obtain ⟨n, hn⟩ := hint
  refine ⟨n, RingOfIntegers.ext ?_⟩
  have h2 : ((a + RingOfIntegers.mapRingHom c a : 𝓞 K) : K) = (a : K) + c a := by
    simp [RingOfIntegers.mapRingHom_apply]
  rw [h2, ← hr, ← hn]
  simp

end PI.OkpW
