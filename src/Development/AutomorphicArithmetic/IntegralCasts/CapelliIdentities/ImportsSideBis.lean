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

namespace EqOneOfPowersNearOne

private lemma key {R : Type} [NormedRing R] [NormedAlgebra ℂ R] {a : R}
    (h : ∀ (p : ℕ), ‖a ^ p - (1 : R)‖ < (1 / 2 : ℝ)) (N : ℕ) :
    (N : ℝ) * ‖a - 1‖ < ‖a - 1‖ * (N / 2) + 1 / 2 := by
  set S : R := ∑ k ∈ Finset.range N, a ^ k with hS
  have hgeom : S * (a - 1) = a ^ N - 1 := geom_sum_mul a N
  have hdiff : (N : R) - S = ∑ k ∈ Finset.range N, ((1 : R) - a ^ k) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hbound : ‖(N : R) - S‖ ≤ N / 2 := by
    rw [hdiff]
    calc ‖∑ k ∈ Finset.range N, ((1 : R) - a ^ k)‖
        ≤ ∑ k ∈ Finset.range N, ‖(1 : R) - a ^ k‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range N, (1 / 2 : ℝ) := by
          apply Finset.sum_le_sum
          intro k _
          rw [norm_sub_rev]; exact (h k).le
      _ = N / 2 := by simp; ring
  have hnorm : ‖(N : R) * (a - 1)‖ = (N : ℝ) * ‖a - 1‖ := by
    have : (N : R) * (a - 1) = (N : ℂ) • (a - 1) := by
      rw [Algebra.smul_def]; simp
    rw [this, norm_smul]; simp
  have hsplit : (N : R) * (a - 1) = ((N : R) - S) * (a - 1) + S * (a - 1) := by
    rw [sub_mul]; abel
  calc (N : ℝ) * ‖a - 1‖ = ‖(N : R) * (a - 1)‖ := hnorm.symm
    _ ≤ ‖((N : R) - S) * (a - 1)‖ + ‖S * (a - 1)‖ := by rw [hsplit]; exact norm_add_le _ _
    _ ≤ ‖(N : R) - S‖ * ‖a - 1‖ + ‖a ^ N - 1‖ := by
        rw [hgeom]; gcongr; exact norm_mul_le _ _
    _ < ‖a - 1‖ * (N / 2) + 1 / 2 := by
        have := h N
        nlinarith [norm_nonneg (a - 1)]

end EqOneOfPowersNearOne

theorem UpperTheory.Reformulated.B.Yhd7.main :
    ∀ {R : Type} [inst : NormedRing R] [NormedAlgebra ℂ R] {a : R},
      (∀ (p : ℕ), ‖a ^ p - (1 : R)‖ < (1 / 2 : ℝ)) → a = (1 : R) := by
  intro R _ _ a h
  by_contra hne
  have hpos : 0 < ‖a - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖a - 1‖)
  have hk := EqOneOfPowersNearOne.key h N
  have h1 : 1 < (N : ℝ) * ‖a - 1‖ := by
    rw [div_lt_iff₀ hpos] at hN; linarith
  nlinarith
