import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open NumberField

namespace GlobalTheory

theorem exists_span_singleton_eq_map_of_integral (K M : Type) [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] (𝔟 : Ideal (𝓞 K)) (β : M) (h𝔟 : 𝔟 ≠ ⊥) (hβ : β ≠ 0)
    (h₁ : ∀ x : K, (∀ b ∈ 𝔟, IsIntegral ℤ (x * (b : K))) → IsIntegral ℤ (β * algebraMap K M x))
    (h₂ : ∀ y ∈ 𝔟, IsIntegral ℤ (β⁻¹ * algebraMap K M (y : K))) :
    ∃ β₀ : 𝓞 M, (β₀ : M) = β ∧ Ideal.span {β₀} = 𝔟.map (algebraMap (𝓞 K) (𝓞 M)) := by
  have hint : IsIntegral ℤ β := by
    have := h₁ 1 (fun b _ => by simpa using RingOfIntegers.isIntegral_coe b)
    simpa using this
  obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : 𝓞 M, (β₀ : M) = β := ⟨⟨β, hint⟩, rfl⟩
  refine ⟨β₀, hβ₀, le_antisymm ?_ ?_⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    have hone : (1 : K) ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) *
        (𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)⁻¹) := by
      rw [FractionalIdeal.coe_ideal_mul_inv 𝔟 h𝔟]
      exact FractionalIdeal.one_mem_one _
    have key : ∀ r ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) *
        (𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)⁻¹),
        ∃ z ∈ 𝔟.map (algebraMap (𝓞 K) (𝓞 M)), (z : M) = β * algebraMap K M r := by
      intro r hr
      refine FractionalIdeal.mul_induction_on
        (C := fun r => ∃ z ∈ 𝔟.map (algebraMap (𝓞 K) (𝓞 M)), (z : M) = β * algebraMap K M r)
        hr ?_ ?_
      · intro i hi j hj
        obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hi
        have h0 : (𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 :=
          FractionalIdeal.coeIdeal_ne_zero.2 h𝔟
        have hj' := (FractionalIdeal.mem_inv_iff h0).1 hj
        have hI : IsIntegral ℤ (β * algebraMap K M j) := by
          refine h₁ j fun c hc => ?_
          obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff _).1
            (hj' _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨c, hc, rfl⟩))
          have : j * (c : K) = (w : K) := hw.symm
          rw [this]
          exact RingOfIntegers.isIntegral_coe w
        refine ⟨algebraMap (𝓞 K) (𝓞 M) b * ⟨_, hI⟩,
          Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hb), ?_⟩
        change algebraMap K M (b : K) * (β * algebraMap K M j) =
          β * algebraMap K M ((b : K) * j)
        rw [map_mul]; ring
      · rintro x y ⟨z, hz, hx⟩ ⟨w, hw, hy⟩
        refine ⟨z + w, Ideal.add_mem _ hz hw, ?_⟩
        change (z : M) + (w : M) = _
        rw [hx, hy, map_add]; ring
    obtain ⟨z, hz, hz'⟩ := key 1 hone
    have : β₀ = z := by
      apply RingOfIntegers.ext
      rw [hz', hβ₀]; simp
    rw [this]; exact hz
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    refine ⟨⟨_, h₂ y hy⟩, ?_⟩
    apply RingOfIntegers.ext
    change β⁻¹ * algebraMap K M (y : K) * (β₀ : M) = algebraMap K M (y : K)
    rw [hβ₀]
    field_simp

theorem abs_norm_eq_absNorm_pow_of_integral (K M : Type) [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] (𝔟 : Ideal (𝓞 K)) (β : M) (h𝔟 : 𝔟 ≠ ⊥) (hβ : β ≠ 0)
    (h₁ : ∀ x : K, (∀ b ∈ 𝔟, IsIntegral ℤ (x * (b : K))) → IsIntegral ℤ (β * algebraMap K M x))
    (h₂ : ∀ y ∈ 𝔟, IsIntegral ℤ (β⁻¹ * algebraMap K M (y : K))) :
    |Algebra.norm ℚ β| = (Ideal.absNorm 𝔟 : ℚ) ^ Module.finrank K M := by
  obtain ⟨β₀, rfl, hspan⟩ := exists_span_singleton_eq_map_of_integral K M 𝔟 β h𝔟 hβ h₁ h₂
  have h := congrArg Ideal.absNorm hspan
  rw [Ideal.absNorm_span_singleton, Ideal.absNorm_algebraMap,
    ← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 M) M] at h
  rw [← Algebra.coe_norm_int, ← Nat.cast_pow, ← h, Nat.cast_natAbs, Int.cast_abs]

theorem sum_log_norm_embedding_eq_finrank_mul_log_absNorm (K M : Type) [Field K] [NumberField K]
    [Field M] [NumberField M] [Algebra K M] (𝔟 : Ideal (𝓞 K)) (β : M) (h𝔟 : 𝔟 ≠ ⊥) (hβ : β ≠ 0)
    (h₁ : ∀ x : K, (∀ b ∈ 𝔟, IsIntegral ℤ (x * (b : K))) → IsIntegral ℤ (β * algebraMap K M x))
    (h₂ : ∀ y ∈ 𝔟, IsIntegral ℤ (β⁻¹ * algebraMap K M (y : K))) :
    ∑ σ : M →+* ℂ, Real.log ‖σ β‖ =
      (Module.finrank K M : ℝ) * Real.log (Ideal.absNorm 𝔟 : ℝ) := by
  have h := abs_norm_eq_absNorm_pow_of_integral K M 𝔟 β h𝔟 hβ h₁ h₂
  have hp : ∏ σ : M →+* ℂ, ‖σ β‖ = ((|Algebra.norm ℚ β| : ℚ) : ℝ) := by
    have h3 := congrArg norm (Algebra.norm_eq_prod_embeddings ℚ ℂ β)
    rw [norm_prod] at h3
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom M ℂ) (fun σ : M →+* ℂ => ‖σ β‖)
      (fun σ : M →ₐ[ℚ] ℂ => ‖σ β‖) (fun _ => rfl), ← h3]
    simp
  rw [← Real.log_prod (fun σ _ => by simpa using hβ), hp, h]
  push_cast
  rw [Real.log_pow]

end GlobalTheory
