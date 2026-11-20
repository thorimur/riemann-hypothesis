import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.PSeries
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
import Std.Tactic.BVDecide.Normalize.Prop
open scoped NNReal ENNReal
open MeasureTheory

namespace GlobalTheory

theorem lintegral_ne_top_of_le_rpow_mul_translate :
    ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] (φ h : G → ℝ≥0∞), Measurable φ →
    ∫⁻ g, φ g ∂μ ≠ ⊤ → ∀ (T : ℕ → Finset G) (c : ℕ) (t : ℝ), (∀ m, 0 < m → (T m).card ≤ m ^ c) → (c : ℝ) + 1 < t →
    (∀ g, ∃ m, 0 < m ∧ ∃ x ∈ T m, h g ≤ (m : ℝ≥0∞) ^ (-t) * φ (x⁻¹ * g)) → ∫⁻ g, h g ∂μ ≠ ⊤ := by
  intro G _ _ _ μ _ φ h hφ hfin T c t hT hct hh
  have hmeas : ∀ (a : ℝ≥0∞) (x : G), Measurable fun g => a * φ (x⁻¹ * g) := fun a x =>
    (hφ.comp (measurable_const_mul _)).const_mul a
  have h1 : ∀ g, h g ≤ ∑' m : ℕ, ∑ x ∈ T (m + 1), ((m + 1 : ℕ) : ℝ≥0∞) ^ (-t) * φ (x⁻¹ * g) := by
    intro g
    obtain ⟨m, hm, x, hx, hle⟩ := hh g
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    refine hle.trans (le_trans ?_ (ENNReal.le_tsum k))
    exact Finset.single_le_sum (f := fun x => ((k + 1 : ℕ) : ℝ≥0∞) ^ (-t) * φ (x⁻¹ * g))
      (fun _ _ => bot_le) hx
  have h2 : ∀ m : ℕ, ∫⁻ g, ∑ x ∈ T (m + 1), ((m + 1 : ℕ) : ℝ≥0∞) ^ (-t) * φ (x⁻¹ * g) ∂μ ≤
      ENNReal.ofReal (((m + 1 : ℕ) : ℝ) ^ ((c : ℝ) - t)) * ∫⁻ g, φ g ∂μ := by
    intro m
    rw [lintegral_finset_sum _ (fun x _ => hmeas _ x)]
    have : ∀ x ∈ T (m + 1), ∫⁻ g, ((m + 1 : ℕ) : ℝ≥0∞) ^ (-t) * φ (x⁻¹ * g) ∂μ =
        ((m + 1 : ℕ) : ℝ≥0∞) ^ (-t) * ∫⁻ g, φ g ∂μ := by
      intro x _
      have hm : Measurable fun g => φ (x⁻¹ * g) := hφ.comp (measurable_const_mul _)
      rw [lintegral_const_mul _ hm,
        lintegral_mul_left_eq_self φ x⁻¹]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, ← mul_assoc]
    gcongr
    have hpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    rw [← ENNReal.ofReal_rpow_of_pos hpos, ENNReal.ofReal_natCast, sub_eq_add_neg,
      ENNReal.rpow_add _ _ (by simp) (by simp), ENNReal.rpow_natCast]
    gcongr
    exact_mod_cast hT (m + 1) (by omega)
  have hs : Summable fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ ((c : ℝ) - t) :=
    (summable_nat_add_iff (f := fun m : ℕ => (m : ℝ) ^ ((c : ℝ) - t)) 1).2
      (Real.summable_nat_rpow.2 (by linarith))
  refine ne_top_of_le_ne_top ?_ (lintegral_mono h1)
  rw [lintegral_tsum (fun m => (Finset.measurable_sum _ (fun x _ => hmeas _ x)).aemeasurable)]
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum h2)
  rw [ENNReal.tsum_mul_right]
  refine ENNReal.mul_ne_top ?_ hfin
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hs]
  exact ENNReal.ofReal_ne_top

end GlobalTheory
