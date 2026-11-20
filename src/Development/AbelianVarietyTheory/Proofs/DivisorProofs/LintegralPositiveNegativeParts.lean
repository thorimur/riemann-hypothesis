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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.FibreParts

theorem lintegral_parts_balance {α : Type} [MeasurableSpace α] (μ : Measure α) (φ : α → ℝ)
    (hφ : Integrable φ μ) :
    (∫⁻ x, ENNReal.ofReal (φ x) ∂μ) + ENNReal.ofReal (-(∫ x, φ x ∂μ)) =
      (∫⁻ x, ENNReal.ofReal (-φ x) ∂μ) + ENNReal.ofReal (∫ x, φ x ∂μ) := by
  have hP : (∫⁻ x, ENNReal.ofReal (φ x) ∂μ) ≠ ⊤ := hφ.lintegral_lt_top.ne
  have hN : (∫⁻ x, ENNReal.ofReal (-φ x) ∂μ) ≠ ⊤ := hφ.neg.lintegral_lt_top.ne
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hφ]
  generalize (∫⁻ x, ENNReal.ofReal (φ x) ∂μ) = P at hP ⊢
  generalize (∫⁻ x, ENNReal.ofReal (-φ x) ∂μ) = N at hN ⊢
  have hp := ENNReal.toReal_nonneg (a := P)
  have hn := ENNReal.toReal_nonneg (a := N)
  rw [← ENNReal.ofReal_toReal hP, ← ENNReal.ofReal_toReal hN]
  simp only [ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hn]
  generalize P.toReal = p at hp ⊢
  generalize N.toReal = n at hn ⊢
  rcases le_total p n with h | h
  · rw [ENNReal.ofReal_of_nonpos (show p - n ≤ 0 by linarith),
      ← ENNReal.ofReal_add hp (by linarith), add_zero]
    congr 1
    ring
  · rw [ENNReal.ofReal_of_nonpos (show -(p - n) ≤ 0 by linarith),
      ← ENNReal.ofReal_add hn (by linarith), add_zero]
    congr 1
    ring

theorem fibre_parts : ∀ (α : Type) [MeasurableSpace α] (μ : Measure α) (a G : ℝ) (φ : α → ℝ), AEMeasurable φ μ → ∫ x, φ x ∂μ = G → (ENNReal.ofReal |a| * ENNReal.ofReal |G| ≤ ∫⁻ x, ENNReal.ofReal |a| * ENNReal.ofReal |φ x| ∂μ) ∧ ((∫⁻ x, ENNReal.ofReal |a| * ENNReal.ofReal |φ x| ∂μ) ≠ ⊤ → (∫⁻ x, (ENNReal.ofReal a * ENNReal.ofReal (φ x) + ENNReal.ofReal (-a) * ENNReal.ofReal (-φ x)) ∂μ) + (ENNReal.ofReal a * ENNReal.ofReal (-G) + ENNReal.ofReal (-a) * ENNReal.ofReal G) = (∫⁻ x, (ENNReal.ofReal a * ENNReal.ofReal (-φ x) + ENNReal.ofReal (-a) * ENNReal.ofReal (φ x)) ∂μ) + (ENNReal.ofReal a * ENNReal.ofReal G + ENNReal.ofReal (-a) * ENNReal.ofReal (-G))) := by
  intro α _ μ a G φ hφ hG
  subst hG
  have habs : ∀ x, ENNReal.ofReal |φ x| = ‖φ x‖ₑ := fun x => by
    rw [← Real.norm_eq_abs, ofReal_norm_eq_enorm]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ⟨?_, fun hfin => ?_⟩
  · refine mul_le_mul_right ?_ _
    simp only [habs]
    rw [← Real.norm_eq_abs, ofReal_norm_eq_enorm]
    exact enorm_integral_le_lintegral_enorm _
  · by_cases ha : a = 0
    · subst ha
      simp
    have hpos : ENNReal.ofReal |a| ≠ 0 := by
      simpa using ha
    have hint : Integrable φ μ := by
      refine ⟨hφ.aestronglyMeasurable, ?_⟩
      unfold HasFiniteIntegral
      simp only [habs] at hfin
      rw [lt_top_iff_ne_top]
      intro h
      exact hfin (by rw [h, ENNReal.mul_top hpos])
    have m1 : AEMeasurable (fun x => ENNReal.ofReal a * ENNReal.ofReal (φ x)) μ :=
      hφ.ennreal_ofReal.const_mul _
    have m2 : AEMeasurable (fun x => ENNReal.ofReal a * ENNReal.ofReal (-φ x)) μ :=
      hφ.neg.ennreal_ofReal.const_mul _
    rw [lintegral_add_left' m1, lintegral_add_left' m2]
    simp only [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have key := lintegral_parts_balance μ φ hint
    generalize (∫⁻ x, ENNReal.ofReal (φ x) ∂μ) = P at key ⊢
    generalize (∫⁻ x, ENNReal.ofReal (-φ x) ∂μ) = N at key ⊢
    generalize ENNReal.ofReal (-(∫ x, φ x ∂μ)) = M at key ⊢
    generalize ENNReal.ofReal (∫ x, φ x ∂μ) = Q at key ⊢
    generalize ENNReal.ofReal (-a) = B
    generalize ENNReal.ofReal a = A
    calc A * P + B * N + (A * M + B * Q) = A * (P + M) + B * (N + Q) := by ring
      _ = A * (N + Q) + B * (P + M) := by rw [key]
      _ = _ := by ring

end GlobalTheory.FibreParts
