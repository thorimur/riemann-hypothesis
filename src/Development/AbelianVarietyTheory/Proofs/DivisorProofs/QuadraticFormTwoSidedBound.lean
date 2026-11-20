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
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff

namespace GlobalTheory

theorem quadForm_comparable_sumSq : ∀ {e : ℕ} (F : (Fin e → ℂ) → (Fin e → ℂ) → ℝ) (S : Set (Fin e → ℂ)), IsCompact S → ContinuousOn (fun p : (Fin e → ℂ) × (Fin e → ℂ) => F p.1 p.2) (S ×ˢ Set.univ) → (∀ z ∈ S, ∀ w, w ≠ 0 → 0 < F z w) → (∀ z w (t : ℝ), F z (t • w) = t ^ 2 * F z w) → ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ z ∈ S, ∀ w, δ * ∑ k, ‖w k‖ ^ 2 ≤ F z w ∧ F z w ≤ C * ∑ k, ‖w k‖ ^ 2 := by
  intro e F S hS hF hpos hhom
  have hF0 : ∀ z, F z 0 = 0 := by
    intro z
    have := hhom z 0 0
    simpa using this
  have hsum_lo : ∀ w : Fin e → ℂ, ‖w‖ ^ 2 ≤ ∑ k, ‖w k‖ ^ 2 := by
    intro w
    have h1 : ‖w‖ ≤ Real.sqrt (∑ k, ‖w k‖ ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 (fun k => ?_)
      refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
      exact Finset.single_le_sum (f := fun k => ‖w k‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ k)
    calc ‖w‖ ^ 2 ≤ (Real.sqrt (∑ k, ‖w k‖ ^ 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = ∑ k, ‖w k‖ ^ 2 := Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => by positivity))
  have hsum_hi : ∀ w : Fin e → ℂ, ∑ k, ‖w k‖ ^ 2 ≤ ((e : ℝ) + 1) * ‖w‖ ^ 2 := by
    intro w
    calc ∑ k, ‖w k‖ ^ 2 ≤ ∑ _k : Fin e, ‖w‖ ^ 2 :=
          Finset.sum_le_sum (fun k _ => pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm w k) 2)
      _ = (e : ℝ) * ‖w‖ ^ 2 := by simp
      _ ≤ ((e : ℝ) + 1) * ‖w‖ ^ 2 := by nlinarith [sq_nonneg ‖w‖]
  set K := S ×ˢ Metric.sphere (0 : Fin e → ℂ) 1 with hKdef
  have hK : IsCompact K := hS.prod (isCompact_sphere _ _)
  have hFK : ContinuousOn (fun p : (Fin e → ℂ) × (Fin e → ℂ) => F p.1 p.2) K :=
    hF.mono (Set.prod_mono le_rfl (Set.subset_univ _))
  have hscale : ∀ z (w : Fin e → ℂ), w ≠ 0 →
      F z w = ‖w‖ ^ 2 * F z (‖w‖⁻¹ • w) ∧ ‖w‖⁻¹ • w ∈ Metric.sphere (0 : Fin e → ℂ) 1 := by
    intro z w hw
    have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
    constructor
    · rw [← hhom z (‖w‖⁻¹ • w) ‖w‖, smul_smul, mul_inv_cancel₀ hn, one_smul]
    · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
        inv_mul_cancel₀ hn]
  rcases K.eq_empty_or_nonempty with hKe | hKn
  · refine ⟨1, 1, one_pos, one_pos, fun z hz w => ?_⟩
    by_cases hw : w = 0
    · subst hw; simp [hF0]
    · exfalso
      have hmem : (z, ‖w‖⁻¹ • w) ∈ K := ⟨hz, (hscale z w hw).2⟩
      rw [hKe] at hmem
      exact hmem
  · obtain ⟨p0, hp0, hmin⟩ := hK.exists_isMinOn hKn hFK
    obtain ⟨p1, hp1, hmax⟩ := hK.exists_isMaxOn hKn hFK
    have hm0 : 0 < F p0.1 p0.2 := by
      refine hpos _ hp0.1 _ ?_
      intro h
      have := hp0.2
      rw [h] at this
      simp at this
    refine ⟨F p0.1 p0.2 / ((e : ℝ) + 1), |F p1.1 p1.2| + 1, by positivity, by positivity,
      fun z hz w => ?_⟩
    by_cases hw : w = 0
    · subst hw; simp [hF0]
    obtain ⟨heq, hu⟩ := hscale z w hw
    have hmem : (z, ‖w‖⁻¹ • w) ∈ K := ⟨hz, hu⟩
    have h1 : F p0.1 p0.2 ≤ F z (‖w‖⁻¹ • w) := (isMinOn_iff.1 hmin) _ hmem
    have h2 : F z (‖w‖⁻¹ • w) ≤ F p1.1 p1.2 := (isMaxOn_iff.1 hmax) _ hmem
    have hlo := hsum_lo w
    have hhi := hsum_hi w
    have hn2 : 0 ≤ ‖w‖ ^ 2 := by positivity
    have he : (0 : ℝ) < (e : ℝ) + 1 := by positivity
    rw [heq]
    constructor
    · rw [div_mul_eq_mul_div, div_le_iff₀ he]
      nlinarith [mul_le_mul_of_nonneg_left hhi hm0.le,
        mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ ((e : ℝ) + 1) * ‖w‖ ^ 2)]
    · nlinarith [mul_le_mul_of_nonneg_left (h2.trans (le_abs_self _)) hn2,
        mul_le_mul_of_nonneg_left hlo (by positivity : (0 : ℝ) ≤ |F p1.1 p1.2| + 1),
        mul_nonneg (abs_nonneg (F p1.1 p1.2)) hn2]

end GlobalTheory
