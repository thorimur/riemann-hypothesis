import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Sheaves.Init

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.FundamentalDomainD5

open Matrix

theorem dot_self_eq_sq_norm {N : ℕ} (v : Fin N → ℝ) :
    v ⬝ᵥ v = ‖(WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm v‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  simp [dotProduct, sq]

theorem cover_round {N : ℕ} (b : Fin N → Fin N → ℝ) (hb : LinearIndependent ℝ b) (ℓ : ℝ)
    (hℓ : ∀ j, b j ⬝ᵥ b j ≤ ℓ ^ 2) (w : Fin N → ℝ) :
    ∃ n : Fin N → ℤ, (w - ∑ j, (n j : ℝ) • b j) ⬝ᵥ (w - ∑ j, (n j : ℝ) • b j) ≤ ((N : ℝ) * ℓ / 2) ^ 2 := by
  classical
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨0, by simp [dotProduct]⟩
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hcard : Fintype.card (Fin N) = Module.finrank ℝ (Fin N → ℝ) := by simp
  let B := basisOfLinearIndependentOfCardEqFinrank hb hcard
  have hB : ∀ j, B j = b j := fun j => by simp [B]
  set c := B.repr w with hcdef
  refine ⟨fun j => round (c j), ?_⟩
  have hw : w = ∑ j, c j • b j := by
    conv_lhs => rw [← B.sum_repr w]
    simp only [hB, hcdef]

  have hdiff : w - ∑ j, ((round (c j) : ℤ) : ℝ) • b j = ∑ j, (c j - round (c j)) • b j := by
    conv_lhs => rw [hw]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [sub_smul]
  have hbj : ∀ j, ‖(WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm (b j)‖ ≤ |ℓ| := by
    intro j
    have h := hℓ j
    rw [dot_self_eq_sq_norm, ← sq_abs ℓ] at h
    by_contra hc
    push_neg at hc
    nlinarith [abs_nonneg ℓ]
  have hnorm : ‖(WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm (∑ j, (c j - round (c j)) • b j)‖ ≤
      (N : ℝ) * |ℓ| / 2 := by
    rw [map_sum]
    calc ‖∑ j, (WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm ((c j - round (c j)) • b j)‖
        ≤ ∑ j, ‖(WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm ((c j - round (c j)) • b j)‖ :=
          norm_sum_le _ _
      _ = ∑ j, |c j - round (c j)| * ‖(WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm (b j)‖ := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [LinearEquiv.map_smul, norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ _j : Fin N, (1 / 2) * |ℓ| :=
          Finset.sum_le_sum (fun j _ =>
            mul_le_mul (abs_sub_round _) (hbj j) (norm_nonneg _) (by norm_num))
      _ = (N : ℝ) * |ℓ| / 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  rw [hdiff, dot_self_eq_sq_norm]
  calc ‖(WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm (∑ j, (c j - round (c j)) • b j)‖ ^ 2
      ≤ ((N : ℝ) * |ℓ| / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = ((N : ℝ) * ℓ / 2) ^ 2 := by
      rw [div_pow, mul_pow, sq_abs, ← mul_pow, ← div_pow]

end Formalism.L2.Pj.FundamentalDomainD5
