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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory

theorem continuous_of_continuous_mul_left_adic {O Γ : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O]
    (h : IsAdic (IsLocalRing.maximalIdeal O)) [TopologicalSpace Γ] {d : O} (hd : d ≠ 0)
    (f : Γ → O) (hf : Continuous fun g => d * f g) : Continuous f := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hϖ
  rw [continuous_iff_continuousAt]
  intro g₀
  have h1 : Filter.Tendsto (fun g => (u * ϖ ^ m) * f g - (u * ϖ ^ m) * f g₀) (nhds g₀) (nhds 0) :=
    tendsto_sub_nhds_zero_iff.mpr (hf.tendsto g₀)
  have h2 : Filter.Tendsto (fun g => f g - f g₀) (nhds g₀) (nhds 0) := by
    rw [h.hasBasis_nhds_zero.tendsto_right_iff] at h1 ⊢
    intro k _
    filter_upwards [h1 (k + m) trivial] with g hg
    simp only [SetLike.mem_coe, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hg ⊢
    rw [← mul_sub, pow_add, mul_assoc, Units.dvd_mul_left, mul_comm (ϖ ^ k)] at hg
    exact (mul_dvd_mul_iff_left (pow_ne_zero m hϖ.ne_zero)).mp hg
  exact tendsto_sub_nhds_zero_iff.mp h2

theorem continuous_block_of_continuous_matrix : ∀ {O Γ : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ [TopologicalSpace Γ] {n r t : ℕ} (M : Γ → Matrix (Fin n) (Fin n) O) (P : Γ → Matrix (Fin r) (Fin r) O) (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O))), Continuous M → (∀ g v, (e (((M g).map (algebraMap O (FractionRing O))).mulVec v)).1 = ((P g).map (algebraMap O (FractionRing O))).mulVec (e v).1) → Continuous P := by
  intro O Γ _ _ _ _ _ h _ n r t M P e hM hP
  refine continuous_matrix fun i j => ?_
  let v : Fin n → FractionRing O := e.symm (Pi.single j 1, 0)
  let w : Fin n → FractionRing O := fun k => (e (Pi.single k 1)).1 i
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) v
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) w
  choose v' hv' using hb
  choose w' hw' using hc
  have hφ : ∀ x : Fin n → FractionRing O, (e x).1 i = ∑ k, x k * w k := by
    intro x
    conv_lhs => rw [pi_eq_sum_univ' x]
    simp [map_sum, Prod.fst_sum, Finset.sum_apply, w]
  have key : ∀ g, ((b : O) * (c : O)) * P g i j = ∑ k, (∑ l, M g k l * v' l) * w' k := by
    intro g
    apply IsFractionRing.injective O (FractionRing O)
    have h1 := congrFun (hP g v) i
    rw [hφ] at h1
    simp only [v, LinearEquiv.apply_symm_apply, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.map_apply] at h1
    simp only [map_mul, map_sum, hv', hw', ← h1, Algebra.smul_def, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [v]
    ring
  refine continuous_of_continuous_mul_left_adic h
    (mul_ne_zero (nonZeroDivisors.coe_ne_zero b) (nonZeroDivisors.coe_ne_zero c)) _ ?_
  simp only [key]
  fun_prop

end GlobalTheory
