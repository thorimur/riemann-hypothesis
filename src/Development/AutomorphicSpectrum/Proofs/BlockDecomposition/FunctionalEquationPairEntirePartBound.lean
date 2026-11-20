import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop

namespace GlobalTheory.CompanionTheory.EisRk1

open MeasureTheory Set Filter Topology

theorem weakFEPair_norm_Λ₀_le (P : WeakFEPair ℂ) {r M : ℝ}
    (hf : ∀ x : ℝ, 1 ≤ x → ‖P.f x - P.f₀‖ ≤ M * x ^ (-r))
    (hg : ∀ x : ℝ, 1 ≤ x → ‖P.g x - P.g₀‖ ≤ M * x ^ (-r))
    (s : ℂ) (hs₁ : s.re < r) (hs₂ : P.k - s.re < r) :
    ‖P.Λ₀ s‖ ≤ M / (r - s.re) + ‖P.ε‖ * M / (r - (P.k - s.re)) := by
  set σ := s.re with hσ
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (by simpa using hf 1 le_rfl)
  set h : ℝ → ℝ := (Ioi 1).indicator (fun t => M * t ^ (σ - 1 - r)) +
      (Ioo 0 1).indicator (fun t => ‖P.ε‖ * M * t ^ (σ - 1 + r - P.k)) with hh
  have hA : IntegrableOn (fun t : ℝ => M * t ^ (σ - 1 - r)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul M
  have hB : IntegrableOn (fun t : ℝ => ‖P.ε‖ * M * t ^ (σ - 1 + r - P.k)) (Ioo 0 1) :=
    (((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := σ - 1 + r - P.k)
      (by linarith)).1).mono_set Ioo_subset_Ioc_self).const_mul _
  have hA' := hA.integrable_indicator measurableSet_Ioi
  have hB' := hB.integrable_indicator measurableSet_Ioo
  have hint : Integrable h (volume.restrict (Ioi 0)) := (hA'.add hB').restrict
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • P.f_modif t‖ ≤ h t := by
    intro t ht
    rw [mem_Ioi] at ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re]
    rcases lt_trichotomy t 1 with h1 | rfl | h1
    · have hinv : 1 < t⁻¹ := (one_lt_inv₀ ht).2 h1
      have e := P.hf_modif_FE t⁻¹ (inv_pos.2 ht)
      rw [one_div, inv_inv] at e
      have hg' : P.g_modif t⁻¹ = P.g t⁻¹ - P.g₀ := by
        simp [WeakFEPair.g_modif, indicator_of_mem (mem_Ioi.2 hinv),
          indicator_of_notMem (notMem_Ioo_of_ge hinv.le)]
      have hval : h t = ‖P.ε‖ * M * t ^ (σ - 1 + r - P.k) := by
        simp [hh, indicator_of_notMem (notMem_Ioi.2 h1.le), indicator_of_mem (mem_Ioo.2 ⟨ht, h1⟩)]
      rw [hval, e, hg', norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos (inv_pos.2 ht) _), Real.inv_rpow ht.le]
      have hb := hg t⁻¹ hinv.le
      rw [Real.inv_rpow ht.le, Real.rpow_neg ht.le, inv_inv] at hb
      have key : t ^ (σ - 1 + r - P.k) = t ^ (σ - 1) * (t ^ P.k)⁻¹ * t ^ r := by
        rw [sub_eq_add_neg (σ - 1 + r), Real.rpow_add ht, Real.rpow_add ht, Real.rpow_neg ht.le]
        ring
      rw [key]
      have hpos : 0 ≤ t ^ (σ - 1) * ‖P.ε‖ * (t ^ P.k)⁻¹ := by positivity
      calc t ^ (σ - 1) * (‖P.ε‖ * (t ^ P.k)⁻¹ * ‖P.g t⁻¹ - P.g₀‖)
          = (t ^ (σ - 1) * ‖P.ε‖ * (t ^ P.k)⁻¹) * ‖P.g t⁻¹ - P.g₀‖ := by ring
        _ ≤ (t ^ (σ - 1) * ‖P.ε‖ * (t ^ P.k)⁻¹) * (M * t ^ r) := mul_le_mul_of_nonneg_left hb hpos
        _ = ‖P.ε‖ * M * (t ^ (σ - 1) * (t ^ P.k)⁻¹ * t ^ r) := by ring
    · have h0 : P.f_modif 1 = 0 := by simp [WeakFEPair.f_modif]
      have hval : h 1 = 0 := by simp [hh]
      rw [h0, hval, norm_zero, mul_zero]
    · have hfm : P.f_modif t = P.f t - P.f₀ := by
        simp [WeakFEPair.f_modif, indicator_of_mem (mem_Ioi.2 h1),
          indicator_of_notMem (notMem_Ioo_of_ge h1.le)]
      have hval : h t = M * t ^ (σ - 1 - r) := by
        simp [hh, indicator_of_mem (mem_Ioi.2 h1), indicator_of_notMem (notMem_Ioo_of_ge h1.le)]
      rw [hfm, hval]
      have hb := hf t h1.le
      have key : t ^ (σ - 1 - r) = t ^ (σ - 1) * t ^ (-r) := by
        rw [sub_eq_add_neg (σ - 1), Real.rpow_add ht]
      rw [key]
      calc t ^ (σ - 1) * ‖P.f t - P.f₀‖ ≤ t ^ (σ - 1) * (M * t ^ (-r)) :=
            mul_le_mul_of_nonneg_left hb (by positivity)
        _ = M * (t ^ (σ - 1) * t ^ (-r)) := by ring
  have hI : ∫ t in Ioi (0 : ℝ), h t = M / (r - σ) + ‖P.ε‖ * M / (r - (P.k - σ)) := by
    rw [hh, integral_add' hA'.restrict hB'.restrict, setIntegral_indicator measurableSet_Ioi,
      setIntegral_indicator measurableSet_Ioo,
      Set.inter_eq_right.2 (Ioi_subset_Ioi zero_le_one), Set.inter_eq_right.2 Ioo_subset_Ioi_self,
      integral_const_mul, integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (by linarith))]
    have hne : σ - 1 + r - P.k + 1 ≠ 0 := by linarith
    rw [Real.one_rpow, Real.one_rpow, Real.zero_rpow hne]
    have h1 : r - σ ≠ 0 := by linarith
    have h2 : r - (P.k - σ) ≠ 0 := by linarith
    have h3 : σ - 1 - r + 1 ≠ 0 := by linarith
    field_simp
    ring
  calc ‖P.Λ₀ s‖ = ‖∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • P.f_modif t‖ := rfl
    _ ≤ ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • P.f_modif t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (0 : ℝ), h t :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hint
          ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ hpt))
    _ = _ := hI

end GlobalTheory.CompanionTheory.EisRk1
