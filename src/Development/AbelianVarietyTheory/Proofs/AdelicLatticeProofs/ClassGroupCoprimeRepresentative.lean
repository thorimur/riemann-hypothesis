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
import Mathlib.RingTheory.ClassGroup.Basic
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
import Mathlib.Topology.Sheaves.Presheaf
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

theorem exists_integral_ideal_in_class_coprime :
    ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K)), m ≠ ⊥ → ∀ c : ClassGroup (𝓞 K), ∃ b : (Ideal (𝓞 K))⁰, ClassGroup.mk0 b = c ∧ (b : Ideal (𝓞 K)) ⊔ m = ⊤ := by
  intro K _ _ m hm c
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective c⁻¹
  have hJ0 : (J : Ideal (𝓞 K)) ≠ 0 := nonZeroDivisors.coe_ne_zero J
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq
    (Ideal.mul_le_inf.trans inf_le_left : (J : Ideal (𝓞 K)) * m ≤ J) (mul_ne_zero hJ0 hm)
  have haJ : a ∈ (J : Ideal (𝓞 K)) := ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  obtain ⟨L, hL⟩ : (J : Ideal (𝓞 K)) ∣ Ideal.span {a} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr haJ)
  have hcop : m ⊔ L = ⊤ := by
    have h1 : (J : Ideal (𝓞 K)) * (m ⊔ L) = J * ⊤ := by
      rw [Ideal.mul_sup, ← hL, ha, Ideal.mul_top]
    exact mul_left_cancel₀ hJ0 h1
  by_cases hL0 : L = 0
  · have hmt : m = ⊤ := by simpa [hL0] using hcop
    obtain ⟨b, hb⟩ := ClassGroup.mk0_surjective c
    exact ⟨b, hb, by simp [hmt]⟩
  · refine ⟨⟨L, mem_nonZeroDivisors_of_ne_zero hL0⟩, ?_, by rw [sup_comm]; exact hcop⟩
    have hprod : ClassGroup.mk0 J * ClassGroup.mk0 ⟨L, mem_nonZeroDivisors_of_ne_zero hL0⟩ = 1 := by
      rw [← map_mul, ClassGroup.mk0_eq_one_iff]
      change ((J : Ideal (𝓞 K)) * L).IsPrincipal
      rw [← hL]
      exact ⟨⟨a, rfl⟩⟩
    rw [hJ] at hprod
    exact (inv_mul_eq_one.mp hprod).symm

end GlobalTheory
